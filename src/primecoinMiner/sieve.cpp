#include "global.h"
#include <assert.h>

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
   free(vfCandidates);
   free(vfCandidateBiTwin);
   free(vfCandidateCunningham1);
   free(vfCompositeCunningham1);
   free(vfCompositeCunningham2);
   free(vfPrimeMultipliers);
   free(vfPrimeMultiplierCounts);
}

void CSieveOfEratosthenes::Init(unsigned int nSieveSize, unsigned int nSievePercentage, unsigned int nSieveExtension, unsigned int nTargetChainLength, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)
{
   //printf("Starting Sieve Initialise... \n");

   unsigned int oldCandidateWords = this->nCandidatesWords;
   unsigned int oldSieveChainLength = this->nSieveChainLength;
   unsigned int oldNumMultiplierRounds = this->nNumMultiplierRounds;
   unsigned int oldPrimeCount = this->nPrimes;

   this->nSieveSize = nSieveSize;
   this->nSievePercentage = nSievePercentage;
   this->nSieveExtension = nSieveExtension;
   this->nChainLength = nTargetChainLength;
   this->nBTCC1ChainLength = (nTargetChainLength + 1) / 2;
   this->nBTCC2ChainLength = nTargetChainLength / 2;
   this->nSieveChainLength = nChainLength + nSieveExtension;
   this->mpzHash = mpzHash;
   this->mpzFixedMultiplier = mpzFixedMultiplier;
   this->nPrimes = (unsigned int)vPrimesSize * nSievePercentage / 100;
   this->nNumMultiplierRounds = (vPrimes[nPrimes-1] / nSieveSize) + 2; // Enough rounds for all prime values.
   this->nCurrentMultiplierRoundPos = 0;
   this->nCurrentWeaveMultiplier = 0;

   this->nCandidatesWords = (nSieveSize + nWordBits - 1) / nWordBits;
   this->nCandidatesBytes = nCandidatesWords * sizeof(sieve_word_t);
   this->nCandidateMultiplier = this->nSieveSize; // Set to max value to force weave.
   this->nCandidateLayer = this->nSieveChainLength; // Set to max value to force weave.

   if (oldCandidateWords != nCandidatesWords)
   {
      // Clear and presize arrays for initial use.
      if (oldCandidateWords != 0)
      {
         free(vfCandidates);
         free(vfCandidateBiTwin);
         free(vfCandidateCunningham1);
      }
      vfCandidates = (sieve_word_t *)malloc(nCandidatesBytes);
      vfCandidateBiTwin = (sieve_word_t *)malloc(nCandidatesBytes);
      vfCandidateCunningham1 = (sieve_word_t *)malloc(nCandidatesBytes);
      memset(vfCandidates, 0, nCandidatesBytes);
      memset(vfCandidateBiTwin, 0, nCandidatesBytes);
      memset(vfCandidateCunningham1, 0, nCandidatesBytes);
   }

   if ((oldCandidateWords != nCandidatesWords) || (oldSieveChainLength != nSieveChainLength))
   {
      if (oldCandidateWords != 0)
      {
         free(vfCompositeCunningham1);
         free(vfCompositeCunningham2);
      }
      vfCompositeCunningham1 = (sieve_word_t *)malloc(nCandidatesBytes * nSieveChainLength);
      vfCompositeCunningham2 = (sieve_word_t *)malloc(nCandidatesBytes * nSieveChainLength);
      memset(vfCompositeCunningham1, 0, (nCandidatesBytes * nSieveChainLength));
      memset(vfCompositeCunningham2, 0, (nCandidatesBytes * nSieveChainLength));
   }

   if ((oldSieveChainLength != nSieveChainLength) 
      || (oldNumMultiplierRounds != nNumMultiplierRounds) 
      || (oldPrimeCount != nPrimes))
   {
      if (oldCandidateWords != 0)
      {
         free(vfPrimeMultipliers);
         free(vfPrimeMultiplierCounts);
      }
      vfPrimeMultipliers = (primeMultiplier_t *)malloc(nNumMultiplierRounds * nPrimes * nSieveChainLength * 2 * sizeof(primeMultiplier_t));
      vfPrimeMultiplierCounts = (int *)malloc(nNumMultiplierRounds * nSieveChainLength * sizeof(int));
      //vfPrimeMultiplierCounts = (int *)malloc(nNumMultiplierRounds * sizeof(int));
   }
   memset(vfPrimeMultiplierCounts, 0, (nNumMultiplierRounds * nSieveChainLength * sizeof(int)));
   //memset(vfPrimeMultiplierCounts, 0, (nNumMultiplierRounds * sizeof(int)));
   //printf("Finished Sieve Initialise... Generating Multipler tables...\n");

   GenerateMultiplierTables();
   //printf("Finished Generating Multipler tables... \n");
}

void CSieveOfEratosthenes::AddMultiplierWithBits(const unsigned int nCurrentMuliplierRound, const unsigned int nLayerNum, const unsigned int nMultiplierBits, const unsigned int nSolvedMultiplier)
{
   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lNumMultiplierRounds = this->nNumMultiplierRounds;
   const unsigned int lPrimes = this->nPrimes;
   const unsigned int lSieveSize = this->nSieveSize;
   //const unsigned int nLayerNum = ((nMultiplierBits >> 20) & 0x000007FF);
   const int nMultiplierPos = (nCurrentMuliplierRound + (nSolvedMultiplier / lSieveSize)) % nNumMultiplierRounds;
   const int nPrimeMultiplierCountPos = vfPrimeMultiplierCounts[(nMultiplierPos * lSieveChainLength) + nLayerNum]++;
   const int nPrimeMultiplierItemPos = (nMultiplierPos * lPrimes * 2 * lSieveChainLength) + (lPrimes * 2  * nLayerNum) + nPrimeMultiplierCountPos;
   //const int nPrimeMultiplierCountPos = vfPrimeMultiplierCounts[nMultiplierPos]++;
   //const int nPrimeMultiplierItemPos = (nMultiplierPos * lPrimes * 2 * lSieveChainLength) + nPrimeMultiplierCountPos;

   vfPrimeMultipliers[nPrimeMultiplierItemPos].nMultiplierBits = nMultiplierBits;
   vfPrimeMultipliers[nPrimeMultiplierItemPos].nMultiplierCandidate = nSolvedMultiplier % lSieveSize;
}

void CSieveOfEratosthenes::AddMultiplier(const unsigned int nCurrentMuliplierRound, const unsigned int nLayerNum, const bool isCunninghamChain1, const unsigned int nPrimeSeq, const unsigned int nSolvedMultiplier)
{
   this->AddMultiplierWithBits(nCurrentMuliplierRound
      ,nLayerNum
      ,(isCunninghamChain1 ? (1U << 31) : 0) | ((nLayerNum & 0x000007FF) << 20) | ( nPrimeSeq & 0x000FFFFF)
      ,nSolvedMultiplier);
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
      for (unsigned int nLayerSeq = 0; nLayerSeq < nSieveChainLength; nLayerSeq++)
      {
         // Find the first number that's divisible by this prime
         AddMultiplier(0, nLayerSeq, true, nPrimeSeq, nFixedInverse);
         AddMultiplier(0, nLayerSeq, false, nPrimeSeq, nPrime - nFixedInverse);
         // For next number in chain
         nFixedInverse = (uint64)nFixedInverse * nTwoInverse % nPrime;
      }
   }

}

void CSieveOfEratosthenes::Weave()
{
   primeStats.nSieveRounds++;
   //
   //printf("Multiplier counts BEFORE weave:\n");
   //for (int i = 0; i < nNumMultiplierRounds ; i++)
   //{
   //   printf("MultiplierPos: %u", i);
   //   for (int j = 0; j < nSieveChainLength; j++)
   //   {
   //      printf(" %u:%u ", j, vfPrimeMultiplierCounts[(i * nSieveChainLength) + j]);
   //   }
   //   printf("\n");
   //}


   primeMultiplier_t* primeMultiplier;
   sieve_word_t* compositeDetail;
   //const uint64 maxValue = (uint64)nSieveSize * (nCurrentMultiplierRoundPos + 1);
   //const uint64 offset = (uint64)nSieveSize * nCurrentMultiplierRoundPos;
   const uint64 maxValue = (uint64)nSieveSize;
   const unsigned int lCurrentMultiplierRoundPos = this->nCurrentMultiplierRoundPos;
   const unsigned int lNumMultiplierRounds = this->nNumMultiplierRounds;
   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lCandidatesBytes = this->nCandidatesBytes;
   const unsigned int lCandidatesWords = this->nCandidatesWords;
   const unsigned int lPrimes = this->nPrimes;
   const unsigned int lSieveSize = this->nSieveSize;
   const int nMultiplierPos = lCurrentMultiplierRoundPos % lNumMultiplierRounds;

   memset(vfCompositeCunningham1, 0, (lCandidatesBytes * lSieveChainLength));
   memset(vfCompositeCunningham2, 0, (lCandidatesBytes * lSieveChainLength));

   for (int layerSeq = 0; layerSeq < lSieveChainLength; layerSeq++)
   {
      //// Ensure this layer is empty before processing multipliers.
      //for (int i = 0; i < nCandidatesWords; i++)
      //{
      //   vfCompositeCunningham1[layerSeq][i] = 0;
      //}
      const int layerPrimeMultiplierOffset = (lPrimes * 2) * layerSeq;
      const int nPrimeMultiplierItemPos = ((nMultiplierPos * lPrimes * 2 * lSieveChainLength) + layerPrimeMultiplierOffset);
      const int numPrimeMultipliers = vfPrimeMultiplierCounts[(nMultiplierPos * lSieveChainLength) + layerSeq];
      //const int nPrimeMultiplierItemPos = (nMultiplierPos * lPrimes * 2 * lSieveChainLength);
      //const int numPrimeMultipliers = vfPrimeMultiplierCounts[nMultiplierPos];
      for (int i = 0 ; i < numPrimeMultipliers; i++)
      {
         primeMultiplier = &vfPrimeMultipliers[nPrimeMultiplierItemPos + i];
         const unsigned int multiplierBits =  primeMultiplier->nMultiplierBits;
         unsigned int variableMultiplier = primeMultiplier->nMultiplierCandidate;
         //const unsigned int layerSeq = ((multiplierBits >> 20) & 0x000007FF);
         const unsigned int lPrimeSeq = multiplierBits & 0x000FFFFF;
         const unsigned int lPrime = vPrimes[lPrimeSeq];
         const bool fIsCunninghamChain1 = (multiplierBits >> 31);
         //compositeDetail = fIsCunninghamChain1 ? vfCompositeCunningham1 : vfCompositeCunningham2;
#ifdef USE_ROTATE
         const unsigned int lRotateBits = lPrime % nWordBits;
         sieve_word_t lBitMask = GetCompositeBitMask(variableMultiplier);
         for (; variableMultiplier < lSieveSize; variableMultiplier += lPrime)
         {
            const unsigned int variableWordNum = GetCandidateWordNum(variableMultiplier);
            const unsigned int wordPos = (layerSeq * lCandidatesWords) + variableWordNum;
            if (fIsCunninghamChain1)
            {
               //_mm_prefetch((const CHAR *)&vfCompositeCunningham1[wordPos + lPrime], _MM_HINT_NTA);
               vfCompositeCunningham1[wordPos] |= lBitMask;
            }
            else
            {
               //_mm_prefetch((const CHAR *)&vfCompositeCunningham2[wordPos + lPrime], _MM_HINT_NTA);
               vfCompositeCunningham2[wordPos] |= lBitMask;
            }
            lBitMask = (lBitMask << lRotateBits) | (lBitMask >> (nWordBits - lRotateBits));
         }
#else
         for (; variableMultiplier < lSieveSize; variableMultiplier += lPrime)
         {
            const unsigned int variableWordNum = GetCandidateWordNum(variableMultiplier);
            const unsigned int wordPos = (layerSeq * lCandidatesWords) + variableWordNum;
            const sieve_word_t lBitMask = GetCompositeBitMask(variableMultiplier);
            if (fIsCunninghamChain1)
            {
               _mm_prefetch((const CHAR *)&vfCompositeCunningham1[wordPos + lPrime], _MM_HINT_NTA);
               vfCompositeCunningham1[wordPos] |= lBitMask;
            }
            else
            {
               _mm_prefetch((const CHAR *)&vfCompositeCunningham2[wordPos + lPrime], _MM_HINT_NTA);
               vfCompositeCunningham2[wordPos] |= lBitMask;
            }
         }
#endif

         AddMultiplierWithBits(nMultiplierPos, layerSeq, multiplierBits, variableMultiplier);
      }
      // All multipliers dealt with for this round, clear layer counts.
      vfPrimeMultiplierCounts[(nMultiplierPos * lSieveChainLength) + layerSeq] = 0;
   }
   //memset(vfPrimeMultiplierCounts + (nMultiplierPos * lSieveChainLength), 0, lSieveChainLength * sizeof(int));
   //vfPrimeMultiplierCounts[nMultiplierPos] = 0;


   //printf("Multiplier counts AFTER weave:\n");
   //for (int i = 0; i < nNumMultiplierRounds ; i++)
   //{
   //   printf("MultiplierPos: %u", i);
   //   for (int j = 0; j < nSieveChainLength; j++)
   //   {
   //      printf(" %u:%u ", j, vfPrimeMultiplierCounts[(i * nSieveChainLength) + j]);
   //   }
   //   printf("\n");
   //}


   // Increment current multiplier round.
   nCurrentMultiplierRoundPos++;
   nCandidateLayer = 0;
   nCandidateMultiplier = 1;
}

void CSieveOfEratosthenes::UpdateCandidateValues()
{
   memset(vfCandidates, 0, nCandidatesBytes);
   memset(vfCandidateBiTwin, 0, nCandidatesBytes);
   memset(vfCandidateCunningham1, 0, nCandidatesBytes);

   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lCandidateLayer = this->nCandidateLayer;
   const unsigned int lCandidateWords = this->nCandidatesWords;
   for (int layerSeq = 0; layerSeq < nChainLength; layerSeq++)
   {
      const unsigned int lCompositeStartIndex = (layerSeq + lCandidateLayer) * lCandidateWords;
      for (int wordNo = 0; wordNo < nCandidatesWords; wordNo++)
      {
         if ((layerSeq < nBTCC1ChainLength) && (layerSeq < nBTCC2ChainLength))
         {
            vfCandidateBiTwin[wordNo] |=  (vfCompositeCunningham1[lCompositeStartIndex + wordNo] | vfCompositeCunningham2[lCompositeStartIndex + wordNo]);
         }
         else if (layerSeq < nBTCC1ChainLength)
         {
            vfCandidateBiTwin[wordNo] |=  vfCompositeCunningham1[lCompositeStartIndex + wordNo];
         }

         vfCandidateCunningham1[wordNo] |= vfCompositeCunningham1[lCompositeStartIndex + wordNo];
         vfCandidates[wordNo] |= vfCompositeCunningham2[lCompositeStartIndex + wordNo];

         if (layerSeq == nChainLength - 1)
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
         if (nCandidateLayer > (nSieveChainLength - nChainLength))
         {
            //if (nCurrentMultiplierRoundPos >= (vPrimes[this->nMaxWeaveMultiplier] - 1)) return false;// 1) return false; //

            // Sieve for more candidates..
            //if (this->nCurrentMultiplierRoundPos == 0)
            //{
            //   //printf("Starting Weave: %u... \n", this->nCurrentMultiplierRoundPos);
            //   this->Weave();
            //   //printf("Finsihed Weave... \n");
            //}
            //else
            //{
            //   this->nCurrentWeaveMultiplier++;
            //   while (this->nCurrentMultiplierRoundPos < vPrimes[this->nCurrentWeaveMultiplier])
            //   {
            //      //printf("Starting Weave: %u... \n", this->nCurrentMultiplierRoundPos);
            //      this->Weave();
            //      //printf("Finsihed Weave... \n");
            //   }
            //}
            //printf("Starting Weave: %u... \n", this->nCurrentMultiplierRoundPos);
            this->Weave();
            //nCandidateLayer = 0;
         }

         // Update Candidate values
         //printf("Starting Updating Candidates: %u... \n", nCandidateLayer);
         this->UpdateCandidateValues();
         //printf("Finsihed Updating Candidates... \n");
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
         nLayerMultiplier = nCandidateLayer;//(1UL << nCandidateLayer); // * (this->nCurrentWeaveMultiplier == 0 ? 1 : vPrimes[this->nCurrentWeaveMultiplier]); 
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