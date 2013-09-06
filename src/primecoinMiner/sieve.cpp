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
   //printf("\nI");

   unsigned int oldCandidateWords = this->nCandidatesWords;
   unsigned int oldSieveChainLength = this->nSieveChainLength;
   unsigned int oldNumMultiplierRounds = this->nNumMultiplierRounds;
   unsigned int oldPrimeCount = this->nPrimes;

   this->nSieveSize = nSieveSize;
   this->nSievePercentage = nSievePercentage;
   this->nChainLength = nTargetChainLength;
   this->nBTCC1ChainLength = (nTargetChainLength + 1) / 2;
   this->nBTCC2ChainLength = nTargetChainLength / 2;

   if (nSieveExtension == -1)
   {
      int extensionCount = 0;
      while ((1UL << extensionCount) < nSieveSize) extensionCount++;
      this->nSieveExtension = nTargetChainLength + extensionCount + 1;
   }
   else
   {
      this->nSieveExtension = nSieveExtension;
   }

   this->nSieveChainLength = this->nChainLength + this->nSieveExtension;
   this->mpzHash = mpzHash;
   this->mpzFixedMultiplier = mpzFixedMultiplier;
   this->nPrimes = (unsigned int)vPrimesSize * nSievePercentage / 100;
   this->nPrimesDoubled = this->nPrimes * 2;
   this->nNumMultiplierRounds = (vPrimes[nPrimes-1] / nSieveSize) + 3; // Enough rounds for all prime values.
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
      vfCompositeCunningham1 = (sieve_word_t*)malloc(nSieveChainLength * nCandidatesBytes);
      vfCompositeCunningham2 = (sieve_word_t*)malloc(nSieveChainLength * nCandidatesBytes);
      memset(vfCompositeCunningham1, 0, (nSieveChainLength * nCandidatesBytes));
      memset(vfCompositeCunningham2, 0, (nSieveChainLength * nCandidatesBytes));
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
      vfPrimeMultipliers = (primeMultiplier_t*)malloc(nNumMultiplierRounds * nPrimesDoubled * nSieveChainLength * sizeof(primeMultiplier_t));
      vfPrimeMultiplierCounts = (unsigned int*)malloc(nNumMultiplierRounds * nSieveChainLength * sizeof(unsigned int));
      memset(vfPrimeMultipliers,0, (nNumMultiplierRounds * nPrimesDoubled * nSieveChainLength * sizeof(primeMultiplier_t)));
   }
   memset(vfPrimeMultiplierCounts, 0, (nNumMultiplierRounds * nSieveChainLength * sizeof(unsigned int)));
   //memset(vfPrimeMultiplierCounts, 0, (nNumMultiplierRounds * sizeof(int)));
   //printf("Finished Sieve Initialise... Generating Multipler tables...\n");

   GenerateMultiplierTables();
   //printf("Finished Generating Multipler tables... \n");
}

void CSieveOfEratosthenes::AddMultiplierWithBits(const unsigned int currentMuliplierRound, const unsigned int layerSeq, const unsigned int multiplierBits, const unsigned int solvedMultiplier)
{
   const unsigned int lNumMultiplierRounds = this->nNumMultiplierRounds;
   const unsigned int lSieveSize = this->nSieveSize;
   const unsigned int multiplierPos = (currentMuliplierRound + (solvedMultiplier / lSieveSize)) % lNumMultiplierRounds;
   //if (nCurrentMultiplierRoundPos > 0)
   //{
   //   int i = 0;
   //   assert(multiplierPos != currentMuliplierRound);
   //}
   const unsigned int primeMultiplierCountPos = vfPrimeMultiplierCounts[GetPrimeMultiplierCountPosition(multiplierPos, layerSeq)]++;
   const unsigned int primeMultiplierItemPos = GetPrimeMultiplierItemPosition(multiplierPos, layerSeq, primeMultiplierCountPos);

   vfPrimeMultipliers[primeMultiplierItemPos].nMultiplierBits = multiplierBits;
   vfPrimeMultipliers[primeMultiplierItemPos].nMultiplierCandidate = solvedMultiplier % lSieveSize;
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
   const unsigned int nTotalPrimes = nPrimes;
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

   //printf("w");

   primeMultiplier_t* primeMultiplier;
   const unsigned int lCurrentMultiplierRoundPos = this->nCurrentMultiplierRoundPos;
   const unsigned int lNumMultiplierRounds = this->nNumMultiplierRounds;
   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lCandidatesBytes = this->nCandidatesBytes;
   const unsigned int lCandidatesWords = this->nCandidatesWords;
   const unsigned int lPrimes = this->nPrimes;
   const unsigned int lSieveSize = this->nSieveSize;
   const unsigned int lRoundIncremental = 1;//(lCurrentMultiplierRoundPos == 0) ? 1: 2;
   const unsigned int lWordBits = this->nWordBits;
   const unsigned int multiplierPos = lCurrentMultiplierRoundPos % lNumMultiplierRounds;

   memset(vfCompositeCunningham1, 0, (lCandidatesBytes * lSieveChainLength));
   memset(vfCompositeCunningham2, 0, (lCandidatesBytes * lSieveChainLength));

   for (int layerSeq = 0; layerSeq < lSieveChainLength; layerSeq++)
   {
      const unsigned int layerOffset = (layerSeq * lCandidatesWords);
      const unsigned int primeMultiplierItemPos = GetPrimeMultiplierItemPosition(multiplierPos, layerSeq, 0);
      const unsigned int numPrimeMultipliers = vfPrimeMultiplierCounts[GetPrimeMultiplierCountPosition(multiplierPos, layerSeq)];
      for (int i = 0 ; i < numPrimeMultipliers; i++)
      {
         primeMultiplier = &vfPrimeMultipliers[primeMultiplierItemPos + i];
         const unsigned int multiplierBits =  primeMultiplier->nMultiplierBits;
         unsigned int variableMultiplier = primeMultiplier->nMultiplierCandidate;
         const unsigned int primeSeq = multiplierBits & 0x000FFFFF;
         const unsigned int prime = vPrimes[primeSeq];
         // Skip 1 whole "round" so we only do odd number multipliers.
         //if (lCurrentMultiplierRoundPos)
         //{
         //   variableMultiplier += ((lSieveSize - variableMultiplier + prime - 1) / prime * prime) - lSieveSize;
         //}
         //const unsigned int layerNo = ((multiplierBits >> 20) & 0x000007FF);
         //assert(layerNo == layerSeq);
         const bool isCunninghamChain1 = (multiplierBits >> 31);
#ifdef USE_ROTATE
         const unsigned int rotateBits = prime % lWordBits;
         sieve_word_t bitMask = GetCompositeBitMask(variableMultiplier);
         for (; variableMultiplier < lSieveSize; variableMultiplier += prime)
         {
            if ((bitMask & 0xAAAAAAAAAAAAAAAA) || !variableMultiplier)
            {
               assert(!variableMultiplier || (variableMultiplier % 2)); // variable multiplier must be 0 or odd;
               const unsigned int variableWordNum = GetCandidateWordNum(variableMultiplier);
               assert(variableWordNum < lCandidatesWords); // make sure wordnum does not exceed candidate wordsize.
               const unsigned int wordPos = layerOffset + variableWordNum;
               assert(wordPos < (lSieveChainLength * lCandidatesBytes)); // make sure wordpos does not exceed array bounds.
               assert(wordPos < ((layerSeq + 1) * lCandidatesWords)); // make sure wordpos does not exceed layer bound
               if (isCunninghamChain1)
               {
                  //_mm_prefetch((const CHAR *)&vfCompositeCunningham1[wordPos + prime], _MM_HINT_NTA);
                  vfCompositeCunningham1[wordPos] |= bitMask;
               }
               else
               {
                  //_mm_prefetch((const CHAR *)&vfCompositeCunningham2[wordPos + prime], _MM_HINT_NTA);
                  vfCompositeCunningham2[wordPos] |= bitMask;
               }
            }
            bitMask = (bitMask << rotateBits) | (bitMask >> (lWordBits - rotateBits));
         }
#else
         for (; variableMultiplier < lSieveSize; variableMultiplier += prime)
         {
            const unsigned int variableWordNum = GetCandidateWordNum(variableMultiplier);
            const unsigned int wordPos = layerOffset + variableWordNum;
            const sieve_word_t bitMask = GetCompositeBitMask(variableMultiplier);
            if (isCunninghamChain1)
            {
               _mm_prefetch((const CHAR *)&vfCompositeCunningham1[wordPos +pPrime], _MM_HINT_NTA);
               vfCompositeCunningham1[wordPos] |= bitMask;
            }
            else
            {
               _mm_prefetch((const CHAR *)&vfCompositeCunningham2[wordPos + prime], _MM_HINT_NTA);
               vfCompositeCunningham2[wordPos] |= bitMask;
            }
         }
#endif

         AddMultiplierWithBits(multiplierPos, layerSeq, multiplierBits, variableMultiplier);
      }
      // All multipliers dealt with for this round, clear layer counts.
      vfPrimeMultiplierCounts[GetPrimeMultiplierCountPosition(multiplierPos, layerSeq)] = 0;
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
   nCurrentMultiplierRoundPos += lRoundIncremental;
   nCandidateLayer = 0;
   nCandidateMultiplier = 0;
}

void CSieveOfEratosthenes::UpdateCandidateValues()
{
   //printf("u");

   memset(vfCandidates, 0x55, nCandidatesBytes);
   memset(vfCandidateBiTwin, 0x55, nCandidatesBytes);
   memset(vfCandidateCunningham1, 0x55, nCandidatesBytes);

   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lCandidateLayer = this->nCandidateLayer;
   const unsigned int lCandidateWords = this->nCandidatesWords;
   for (int layerSeq = 0; layerSeq < nChainLength; layerSeq++)
   {
      const unsigned int lCompositeStartIndex = (layerSeq + lCandidateLayer) * lCandidateWords;
      for (int wordNo = 0; wordNo < nCandidatesWords; wordNo++)
      {
         if ((!layerSeq) && (!wordNo))
         {
            vfCandidates[wordNo] = 0x5555555555555554;
            vfCandidateCunningham1[wordNo] = 0x5555555555555554;
            vfCandidateBiTwin[wordNo] = 0x5555555555555554;
         }

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
   nCandidateMultiplier = 0;
   //primeStats.nCandidateCount += this->GetCandidateCount();
}

bool CSieveOfEratosthenes::GetNextCandidateMultiplier(unsigned int& nVariableMultiplier, unsigned int& nLayerMultiplier, unsigned int& nCandidateType)
{
   //printf("-G");

   unsigned int lWordNum;
   sieve_word_t lBits;
   sieve_word_t lBitMask;

   while (true)
   {
      if (nCandidateMultiplier)
         nCandidateMultiplier += 2;
      else
         nCandidateMultiplier++;

      if (nCandidateMultiplier >= nSieveSize) 
      {
         nCandidateLayer++;
         if (nCandidateLayer > (nSieveChainLength - nChainLength))
         {
            if (nCurrentMultiplierRoundPos >= 60) return false; //(vPrimes[this->nMaxWeaveMultiplier] - 1)) return false;//1) return false; // 

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
            //if (nCurrentMultiplierRoundPos % 2 == 0) this->Weave(); //Double weave to land up on an odd base.. even bases are tested via sieve extensions.
            //nCandidateLayer = 0;
         }

         // Update Candidate values
         //printf("Starting Updating Candidates: %u... \n", nCandidateLayer);
         this->UpdateCandidateValues();
         //printf("Finsihed Updating Candidates... \n");
         continue;
      }

      assert(nCandidateMultiplier % 2); // must be an odd number

      lWordNum = GetCandidateWordNum(nCandidateMultiplier);
      lBits = vfCandidates[lWordNum];
      if (nCandidateMultiplier % nWordBits == 0)
      {
         while (lBits == 0 && nCandidateMultiplier < nSieveSize)
         {
            // Skip an entire word
            nCandidateMultiplier += nWordBits;
            lWordNum = GetCandidateWordNum(nCandidateMultiplier);
            lBits = vfCandidates[lWordNum];
         }
      }
      //if (nCandidateMultiplier % nWordBits == 0)
      //{
      //   // Update the current word
      //   lBits = vfCandidates[lWordNum];

      //   // Check if any bits are set
      //   if (lBits == 0)
      //   {
      //      // Skip an entire word
      //      nCandidateMultiplier += nWordBits - 1;
      //      continue;
      //   }
      //}

      if (nCandidateMultiplier >= nSieveSize) continue;

      lBitMask = GetCompositeBitMask(nCandidateMultiplier);
      if (lBits & lBitMask)
      {
         primeStats.nCandidateCount ++;

         nVariableMultiplier = nCandidateMultiplier + ((this->nCurrentMultiplierRoundPos -1) * nSieveSize);
         //printf("%u",nVariableMultiplier);
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