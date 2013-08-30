#include "global.h"

static unsigned int int_invert(unsigned int a, unsigned int nPrime)
{
   // Extended Euclidean algorithm to calculate the inverse of a in finite field defined by nPrime
   int rem0 = nPrime, rem1 = a % nPrime, rem2;
   int aux0 = 0, aux1 = 1, aux2;
   int quotient, inverse;

   while (1)
   {
      if (rem1 <= 1)
      {
         inverse = aux1;
         break;
      }

      rem2 = rem0 % rem1;
      quotient = rem0 / rem1;
      aux2 = -quotient * aux1 + aux0;

      if (rem2 <= 1)
      {
         inverse = aux2;
         break;
      }

      rem0 = rem1 % rem2;
      quotient = rem1 / rem2;
      aux0 = -quotient * aux2 + aux1;

      if (rem0 <= 1)
      {
         inverse = aux0;
         break;
      }

      rem1 = rem2 % rem0;
      quotient = rem2 / rem0;
      aux1 = -quotient * aux0 + aux2;
   }

   return (inverse + nPrime) % nPrime;
}

CSieveOfEratosthenes::~CSieveOfEratosthenes(void)
{
   vfCandidates.clear();
   vfCandidateBiTwin.clear();
   vfCandidateCunningham1.clear();
   vfCompositeCunningham1.clear();
   vfCompositeCunningham2.clear();
   vfPrimeMultipliers.clear();
}

void CSieveOfEratosthenes::Init(unsigned int nSieveSize, unsigned int nSievePercentage, unsigned int nSieveExtension, unsigned int nTargetChainLength, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)
{
   this->nSieveSize = nSieveSize;
   this->nSievePercentage = nSievePercentage;
   this->nSieveExtension = nSieveExtension;
   this->nChainLength = nTargetChainLength;
   this->nBTCC1ChainLength = (nTargetChainLength + 1) / 2;
   this->nBTCC2ChainLength = nTargetChainLength / 2;
   this->nDoubleChainLength = nChainLength + nSieveExtension;
   this->mpzHash = mpzHash;
   this->mpzFixedMultiplier = mpzFixedMultiplier;
   this->nPrimes = (unsigned int)vPrimesSize * nSievePercentage / 100;
   this->nNumMultiplierRounds = (vPrimes[nPrimes-1] / nSieveSize) + 1; // Enough rounds for all prime values.
   this->nCurrentMultiplierRoundPos = 0;
   this->nCurrentWeaveMultiplier = 0;

   this->nCandidatesWords = (nSieveSize + nWordBits - 1) / nWordBits;
   this->nCandidatesBytes = nCandidatesWords * sizeof(sieve_word_t);
   this->nCandidateMultiplier = this->nSieveSize; // Set to max value to force weave.
   this->nCandidateLayer = this->nDoubleChainLength; // Set to max value to force weave.

   // Clear and presize vectors for initial use.
   vfCandidates.clear();
   vfCandidateBiTwin.clear();
   vfCandidateCunningham1.clear();
   vfCandidates.reserve(nCandidatesWords);
   vfCandidateBiTwin.reserve(nCandidatesWords);
   vfCandidateCunningham1.reserve(nCandidatesWords);
   for (int i = 0; i < nCandidatesWords; i++)
   {
      vfCandidates.emplace_back();
      vfCandidateBiTwin.emplace_back();
      vfCandidateCunningham1.emplace_back();
      vfCandidates[i] = 0;
      vfCandidateBiTwin[i] = 0;
      vfCandidateCunningham1[i] = 0;
   }

   vfCompositeCunningham1.clear();
   vfCompositeCunningham2.clear();
   vfCompositeCunningham1.reserve(nDoubleChainLength);
   vfCompositeCunningham2.reserve(nDoubleChainLength);
   for (int i = 0; i < nDoubleChainLength; i++)
   {
      vfCompositeCunningham1.emplace_back();
      vfCompositeCunningham2.emplace_back();
      vfCompositeCunningham1[i].clear();
      vfCompositeCunningham2[i].clear();
      vfCompositeCunningham1[i].reserve(nCandidatesWords);
      vfCompositeCunningham2[i].reserve(nCandidatesWords);
      for (int j = 0; j < nCandidatesWords; j++)
      {
         vfCompositeCunningham1[i].emplace_back();
         vfCompositeCunningham2[i].emplace_back();
         vfCompositeCunningham1[i][j] = 0;
         vfCompositeCunningham2[i][j] = 0;
      }
   }

   int noPrimesPerRound = (nPrimes / nNumMultiplierRounds) * 2;
   int noMultiplierRounds = nNumMultiplierRounds + 1;
   vfPrimeMultipliers.clear();
   vfPrimeMultipliers.reserve(noMultiplierRounds);
   for (int i = 0; i < noMultiplierRounds; i++)
   {
      vfPrimeMultipliers.emplace_back();
      vfPrimeMultipliers[i].clear();
      vfPrimeMultipliers[i].reserve(nDoubleChainLength);
      for (int j = 0; j < nDoubleChainLength; j++)
      {
         vfPrimeMultipliers[i].emplace_back();
         vfPrimeMultipliers[i][j].clear();
         vfPrimeMultipliers[i][j].reserve(noPrimesPerRound);
      }
   }

   GenerateMultiplierTables();
}

void CSieveOfEratosthenes::AddMultiplier(const unsigned int nLayerNum, const bool isCunninghamChain1, const unsigned int nPrimeSeq, const unsigned int nSolvedMultiplier)
{
   int nMultiplierPos = nSolvedMultiplier / nSieveSize;
   vfPrimeMultipliers[nMultiplierPos][nLayerNum].emplace_back();
   primeMultiplier_t* nPrimeMultiplier = &vfPrimeMultipliers[nMultiplierPos][nLayerNum].back(); 
   nPrimeMultiplier->nMultiplierBits = (isCunninghamChain1 ? (1U << 31) : 0) | ((nLayerNum & 0x000007FF) << 20) | ( nPrimeSeq & 0x000FFFFF);
   nPrimeMultiplier->nMultiplierCandidate = nSolvedMultiplier;
}

bool CSieveOfEratosthenes::GenerateMultiplierTables()
{
   const unsigned int nTotalPrimes = vPrimesSize;
   const unsigned int nTotalPrimesLessOne = nTotalPrimes-1;

   mpz_class mpzFixedFactor = mpzHash * mpzFixedMultiplier;
   unsigned int nFixedFactorCombinedMod = 0;
   unsigned int nCombinedEndSeq = nMinPrimeSeq;

   for (unsigned int nPrimeSeq = nMinPrimeSeq; nPrimeSeq < nPrimes; nPrimeSeq++)
   {
      unsigned int nPrime = vPrimes[nPrimeSeq];
      if (nPrimeSeq >= nCombinedEndSeq)
      {
         // Combine multiple primes to produce a big divisor
         unsigned int nPrimeCombined = 1;
         while (nPrimeCombined < UINT_MAX / vPrimes[nCombinedEndSeq] && nCombinedEndSeq < nTotalPrimesLessOne )
         {
            nPrimeCombined *= vPrimes[nCombinedEndSeq];
            nCombinedEndSeq++;
         }

         nFixedFactorCombinedMod = mpz_tdiv_ui(mpzFixedFactor.get_mpz_t(), nPrimeCombined);
      }

      unsigned int nFixedFactorMod = nFixedFactorCombinedMod % nPrime;
      if (nFixedFactorMod == 0)
      {
         // Nothing in the sieve will be divisible by this prime
         continue;
      }

      // Find the modulo inverse of fixed factor
      unsigned int nFixedInverse = int_invert(nFixedFactorMod, nPrime);
      if (!nFixedInverse)
         return error("CSieveOfEratosthenes::GenerateMultiplierTables(): int_invert of fixed factor failed for prime #%u=%u", nPrimeSeq, vPrimes[nPrimeSeq]);
      unsigned int nTwoInverse = (nPrime + 1) / 2;

      // Weave the sieve for the prime
      for (unsigned int nLayerSeq = 0; nLayerSeq < nDoubleChainLength; nLayerSeq++)
      {
         // Find the first number that's divisible by this prime
         AddMultiplier(nLayerSeq, true, nPrimeSeq, nFixedInverse);
         AddMultiplier(nLayerSeq, false, nPrimeSeq, nPrime - nFixedInverse);
         // For next number in chain
         nFixedInverse = (uint64)nFixedInverse * nTwoInverse % nPrime;
      }
   }

}

void CSieveOfEratosthenes::Weave()
{
   primeStats.nSieveRounds++;

   primeMultiplier_t* primeMultiplier;
   std::vector<sieve_word_t>* compositeDetail;
   //const uint64 maxValue = (uint64)nSieveSize * (nCurrentMultiplierRoundPos + 1);
   //const uint64 offset = (uint64)nSieveSize * nCurrentMultiplierRoundPos;
   const uint64 maxValue = (uint64)nSieveSize;
   for (int layerSeq = 0; layerSeq < nDoubleChainLength; layerSeq++)
   {
      int numPrimeMultipliers = vfPrimeMultipliers[nCurrentMultiplierRoundPos % nNumMultiplierRounds][layerSeq].size();
      for (int i = 0 ; i < numPrimeMultipliers; i++)
      {
         primeMultiplier = &vfPrimeMultipliers[nCurrentMultiplierRoundPos % nNumMultiplierRounds][layerSeq][i];
         unsigned int variableMultiplier = primeMultiplier->nMultiplierCandidate;
         unsigned int multiplierBits =  primeMultiplier->nMultiplierBits;
         unsigned int nPrime = vPrimes[multiplierBits & 0x000FFFFF];

         unsigned int chaintype = (multiplierBits >> 31);

         compositeDetail = (multiplierBits >> 31) ? &vfCompositeCunningham1[layerSeq] : &vfCompositeCunningham2[layerSeq];
         do
         {
            (*compositeDetail)[GetCandidateWordNum(variableMultiplier)] |= GetCompositeBitMask(variableMultiplier);
            variableMultiplier += nPrime;
         }while (variableMultiplier < maxValue);

         int nextMultiplierRound = (nCurrentMultiplierRoundPos + (variableMultiplier / nSieveSize)) % nNumMultiplierRounds;
         vfPrimeMultipliers[nextMultiplierRound][layerSeq].emplace_back();
         primeMultiplier =  &vfPrimeMultipliers[nextMultiplierRound][layerSeq].back();
         primeMultiplier->nMultiplierBits = multiplierBits;
         primeMultiplier->nMultiplierCandidate = variableMultiplier % this->nSieveSize;
      }

      // All multipliers dealt with for this layer, clear it and move on.
      vfPrimeMultipliers[nCurrentMultiplierRoundPos % nNumMultiplierRounds][layerSeq].clear();
   }

   // Increment current multiplier round.
   nCurrentMultiplierRoundPos++;
   nCandidateLayer = 0;
   nCandidateMultiplier = 1;
}

void CSieveOfEratosthenes::UpdateCandidateValues()
{
   for (int i = 0; i < nChainLength; i++)
   {
      for (int wordNo = 0; wordNo < nCandidatesWords; wordNo++)
      {
         if (i == 0)
         {
            vfCandidateBiTwin[wordNo] = vfCandidateCunningham1[wordNo] =  vfCandidates[wordNo] = 0;
         }

         if ((i < nBTCC1ChainLength) && (i < nBTCC2ChainLength))
         {
            vfCandidateBiTwin[wordNo] |=  (vfCompositeCunningham1[nCandidateLayer + i][wordNo] | vfCompositeCunningham2[nCandidateLayer + i][wordNo]);
         }
         else if (i < nBTCC1ChainLength)
         {
            vfCandidateBiTwin[wordNo] |=  vfCompositeCunningham1[nCandidateLayer + i][wordNo];
         }

         vfCandidateCunningham1[wordNo] |= vfCompositeCunningham1[nCandidateLayer + i][wordNo];
         vfCandidates[wordNo] |= vfCompositeCunningham2[nCandidateLayer + i][wordNo];

         if (i == nChainLength - 1)
         {
            vfCandidates[wordNo] = ~(vfCandidateCunningham1[wordNo] & vfCandidates[wordNo] & vfCandidateBiTwin[wordNo]);
            vfCandidateCunningham1[wordNo] = ~(vfCandidateCunningham1[wordNo]);
            vfCandidateBiTwin[wordNo] = ~(vfCandidateBiTwin[wordNo]);
         }
      }
   }
   nCandidateMultiplier = 1;
}

bool CSieveOfEratosthenes::GetNextCandidateMultiplier(unsigned int& nVariableMultiplier, unsigned int& nLayerMultiplier, unsigned int& nCandidateType)
{
   unsigned int lWordNum;
   sieve_word_t lBits;
   sieve_word_t lBitMask;

   while (true)
   {
      nCandidateMultiplier++;
      if (nCandidateMultiplier >= nSieveSize) 
      {
         nCandidateLayer++;
         if (nCandidateLayer > (nDoubleChainLength - nChainLength))
         {
            if (nCurrentMultiplierRoundPos >= vPrimes[this->nMaxWeaveMultiplier]) return false;// 1) return false; //

            // Sieve for more candidates..
            if (this->nCurrentMultiplierRoundPos == 0)
            {
               this->Weave();
            }
            else
            {
               this->nCurrentWeaveMultiplier++;
               while (this->nCurrentMultiplierRoundPos < vPrimes[this->nCurrentWeaveMultiplier])
                  this->Weave();
            }
            //this->Weave();
            nCandidateLayer = 0;
         }

         // Update Candidate values
         this->UpdateCandidateValues();
      }
      lWordNum = GetCandidateWordNum(nCandidateMultiplier);
      lBits = vfCandidates[lWordNum];
      if (lBits == 0)
      {
         // Skip an entire word
         nCandidateMultiplier += nWordBits - 1;
         continue;
      }

      lBitMask = GetCompositeBitMask(nCandidateMultiplier);
      if (lBits & lBitMask)
      {
         nVariableMultiplier = nCandidateMultiplier + ((this->nCurrentMultiplierRoundPos -1) * nSieveSize);
         nLayerMultiplier = (1UL << nCandidateLayer); // * (this->nCurrentWeaveMultiplier == 0 ? 1 : vPrimes[this->nCurrentWeaveMultiplier]); 
         if (vfCandidateBiTwin[lWordNum] & lBitMask)
            nCandidateType = PRIME_CHAIN_BI_TWIN;
         else if (vfCandidateCunningham1[lWordNum] & lBitMask)
            nCandidateType = PRIME_CHAIN_CUNNINGHAM1;
         else
            nCandidateType = PRIME_CHAIN_CUNNINGHAM2;
         return true;
      }

   }

   return true;
}