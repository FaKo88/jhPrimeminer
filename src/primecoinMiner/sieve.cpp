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

void CSieveOfEratosthenes::Init(unsigned int nSieveSize, unsigned int nSievePercentage, unsigned int nTargetChainLength, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)
{
   this->nSieveSize = nSieveSize;
   this->nSievePercentage = nSievePercentage;
   this->nChainLength = nTargetChainLength;
   this->nBTCC1ChainLength = (nTargetChainLength + 1) / 2;
   this->nBTCC2ChainLength = nTargetChainLength / 2;
   this->nDoubleChainLength = nChainLength *2;
   this->mpzHash = mpzHash;
   this->mpzFixedMultiplier = mpzFixedMultiplier;
   this->nPrimes = (unsigned int)vPrimesSize * nSievePercentage / 100;
   this->nNumMultiplierRounds = (vPrimes[nPrimes] / nSieveSize) + 1; // Enough rounds for all prime values.
   this->nCurrentMultiplierRoundPos = 0;

   this->nMaxMultiplierRoundPos = ??

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

   vfCompositeCunningham1.clear();
   vfCompositeCunningham2.clear();
   vfCompositeCunningham1.reserve(nDoubleChainLength);
   vfCompositeCunningham2.reserve(nDoubleChainLength);
   for (int i = 0; i < nDoubleChainLength; i++)
   {
      vfCompositeCunningham1[i].clear();
      vfCompositeCunningham2[i].clear();
      vfCompositeCunningham1[i].reserve(nCandidatesWords);
      vfCompositeCunningham2[i].reserve(nCandidatesWords);
   }

   int noPrimesPerRound = (nPrimes / nNumMultiplierRounds) * 2;
   int noMultiplierRounds = nNumMultiplierRounds + 1;
   vfPrimeMultipliers.clear();
   vfPrimeMultipliers.reserve(noMultiplierRounds);
   for (int i = 0; i < noMultiplierRounds; i++)
   {
      vfPrimeMultipliers[i].clear();
      vfPrimeMultipliers[i].reserve(nDoubleChainLength);
      for (int j = 0; j < nDoubleChainLength; j++)
      {
         vfPrimeMultipliers[i][j].clear();
         vfPrimeMultipliers[i][j].reserve(noPrimesPerRound);
      }
   }

   GenerateMultiplierTables();
}

void CSieveOfEratosthenes::AddMultiplier(const unsigned int nLayerNum, const bool isCunninghamChain1, const unsigned int nPrimeSeq, const unsigned int nSolvedMultiplier)
{
   int nMultiplierPos = nSolvedMultiplier / nNumMultiplierRounds;
   vfPrimeMultipliers[nMultiplierPos][nLayerNum].emplace_back();
   primeMultiplier_t* nPrimeMultiplier = &vfPrimeMultipliers[nMultiplierPos][nLayerNum].back(); 
   nPrimeMultiplier->nMultiplierBits = (isCunninghamChain1 ? (1U << 31) : 0) | ((nLayerNum & 0x000007FF) << 20) | ( nPrimeSeq & 0x000FFFFF);
   nPrimeMultiplier->nMultiplierCandidate = nSolvedMultiplier;
}

bool CSieveOfEratosthenes::GenerateMultiplierTables()
{
   //const unsigned int nTotalPrimes = vPrimesSize;
   //const unsigned int nTotalPrimesLessOne = nTotalPrimes-1;

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
         while (nPrimeCombined < UINT_MAX / vPrimes[nCombinedEndSeq])// this clause never likely to happen: && nCombinedEndSeq < nTotalPrimesLessOne )
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
   primeMultiplier_t* primeMultiplier;
   std::vector<sieve_word_t>* compositeDetail;
   int maxValue = (nSieveSize * (nCurrentMultiplierRoundPos + 1));
   for (int layerSeq = 0; layerSeq < nDoubleChainLength; layerSeq++)
   {
      int numPrimeMultipliers = vfPrimeMultipliers[nCurrentMultiplierRoundPos][layerSeq].size();
      for (int i = 0 ; i < numPrimeMultipliers; i++)
      {
         primeMultiplier = &vfPrimeMultipliers[nCurrentMultiplierRoundPos][layerSeq][i];
         unsigned int variableMultiplier = primeMultiplier->nMultiplierCandidate;
         unsigned int multiplierBits =  primeMultiplier->nMultiplierBits;
         unsigned int nPrime = vPrimes[multiplierBits & 0x000FFFFF];
         compositeDetail = (multiplierBits >> 31) ? &vfCompositeCunningham1[layerSeq] : &vfCompositeCunningham2[layerSeq];
         do
         {
            (*compositeDetail)[GetCandidateWordNum(variableMultiplier)] |= GetCompositeBitMask(variableMultiplier);
            variableMultiplier += nPrime;
         }while (variableMultiplier < maxValue);

         int nextMultiplierRound = ((nCurrentMultiplierRoundPos + 1) + (variableMultiplier / nSieveSize)) % nNumMultiplierRounds;
         vfPrimeMultipliers[nextMultiplierRound][layerSeq].emplace_back();
         primeMultiplier =  &vfPrimeMultipliers[nextMultiplierRound][layerSeq].back();
         primeMultiplier->nMultiplierBits = multiplierBits;
         primeMultiplier->nMultiplierCandidate = variableMultiplier;
      }

      // All multipliers dealt with for this layer, clear it and move on.
      vfPrimeMultipliers[nCurrentMultiplierRoundPos][layerSeq].clear();
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

         vfCandidates[wordNo] |= (vfCompositeCunningham1[nCandidateLayer + i][wordNo] & vfCompositeCunningham2[nCandidateLayer + i][wordNo]);
         vfCandidateCunningham1[wordNo] |= vfCompositeCunningham1[nCandidateLayer + i][wordNo];

         if (i == nChainLength - 1)
         {
            vfCandidates[wordNo] = ~(vfCandidates[wordNo] & vfCandidateBiTwin[wordNo]);
            vfCandidateCunningham1[wordNo] = ~(vfCandidateCunningham1[wordNo]);
            vfCandidateBiTwin[wordNo] = ~(vfCandidateBiTwin[wordNo]);
         }
      }
   }
   nCandidateMultiplier = 1;
}

bool CSieveOfEratosthenes::GetNextCandidateMultiplier(unsigned int& nVariableMultiplier, unsigned int& nCandidateType)
{
   unsigned int lWordNum = GetCandidateWordNum(nCandidateMultiplier);
   sieve_word_t lBits = vfCandidates[lWordNum];
   sieve_word_t lBitMask;

   while (true)
   {
      nCandidateMultiplier++;
      if (nCandidateMultiplier >= nSieveSize) 
      {
         if (nCandidateLayer >= nDoubleChainLength)
         {
            if (nCurrentMultiplierRoundPos >= nMaxMultiplierRoundPos) return false;

            // Sieve for more candidates..
            this->Weave();
         }
         else
         {
            // Work out next layer
            nCandidateLayer++;
            this->UpdateCandidateValues();
         }
      }
      if (nCandidateMultiplier % nWordBits == 0)
      {
         lWordNum = GetCandidateWordNum(nCandidateMultiplier);
         lBits = vfCandidates[lWordNum];
         if (lBits == 0)
         {
            // Skip an entire word
            nCandidateMultiplier += nWordBits - 1;
            continue;
         }
      }
      lBitMask = GetCompositeBitMask(nCandidateMultiplier);
      if (lBits & lBitMask)
      {
         nVariableMultiplier = nCandidateMultiplier;
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