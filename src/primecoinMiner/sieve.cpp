#include "global.h"
#include "sha256.h"
#include <iostream>
#include <fstream>
#include <algorithm>
#ifdef _DEBUG
#include <assert.h>
#endif

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
   vfCandidateCunningham1.clear();
   vfCandidateBiTwin.clear();
   vfComposites.clear();
   vfCC1PrimeMultipliers.clear();
   vfCC2PrimeMultipliers.clear();
   vfExtendedCC1PrimesToWeave.clear();
   vfExtendedCC2PrimesToWeave.clear();
}

void CSieveOfEratosthenes::Init(unsigned int nSieveSize, unsigned int numPrimes, unsigned int targetChainLength, unsigned int btTargetChainLength, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)
{
   //printf("Starting Sieve Initialise... \n");
   //printf("\nI");

   unsigned int oldCandidateWords = this->nCandidatesWords;
   unsigned int oldSieveChainLength = this->nSieveChainLength;
   unsigned int oldNumMultiplierRounds = this->nNumMultiplierRounds;
   unsigned int oldPrimeCount = this->nPrimes;

   this->nSieveSize = nSieveSize;
   this->nHalfSieveSize = nSieveSize >> 1; // divide by 2
   this->nChainLength = targetChainLength;
   this->nBTCC1ChainLength = floor((btTargetChainLength + 1) / 2);
   this->nBTCC2ChainLength = floor(btTargetChainLength / 2);

   int extensionCount = 0;
   while ((1UL << extensionCount) < nSieveSize) extensionCount++;
   this->nSieveExtension = max(targetChainLength,btTargetChainLength) + extensionCount + 1;
   primeStats.nSieveLayers = this->nSieveExtension;

   this->nSieveChainLength = this->nChainLength + this->nSieveExtension;
   this->mpzHash = mpzHash;
   this->mpzFixedMultiplier = mpzFixedMultiplier;
   this->nPrimes = numPrimes;

#ifdef DEBUG_SIEVE
   std::ofstream sieveLog;
   sieveLog.open("SieveDebug.log", std::ios::out | std::ios::app);
   if (sieveLog.is_open())
   {
      sieveLog << "H" << "\t" << this->mpzHash.get_str(16).c_str() << "\t" << this->mpzFixedMultiplier.get_str(16).c_str() << std::endl;
      sieveLog.close();
   }
#endif

   this->nPrimesDoubled = this->nPrimes * 2;
   this->nNumMultiplierRounds = (vPrimes[nPrimes-1] / nSieveSize) + 3; // Enough rounds for all prime values.
   this->nCurrentMultiplierRoundPos = 0;
   this->nCurrentWeaveMultiplier = 0;
   this->nMaxWeaveMultiplier = max(4, ceil(4096000 / this->nSieveSize)); // Enough rounds to get candidate numbers > 4mill.

   this->nCandidatesWords = (nSieveSize + nWordBits - 1) / nWordBits;
   this->nCandidatesBytes = nCandidatesWords * sizeof(sieve_word_t);
   this->nCandidateMultiplier = this->nSieveSize; // Set to max value to force weave.
   this->nCandidateLayer = this->nSieveChainLength; // Set to max value to force weave.
   this->nMaxCandidateLayer = this->nSieveChainLength - this->nChainLength;

   if (oldCandidateWords < nCandidatesWords)
   {
      // Clear and presize arrays for initial use.
      if (oldCandidateWords == 0)
      {
         vfCandidates.clear();
         vfCandidateCunningham1.clear();
         vfCandidateBiTwin.clear();
      }
      vfCandidates.resize(this->nCandidatesWords);
      vfCandidateCunningham1.resize(this->nCandidatesWords);
      vfCandidateBiTwin.resize(this->nCandidatesWords);
      memset(&vfCandidates[0], 0, nCandidatesBytes);
      memset(&vfCandidateCunningham1[0], 0, nCandidatesBytes);
      memset(&vfCandidateBiTwin[0], 0, nCandidatesBytes);
   }

   if ((oldCandidateWords < nCandidatesWords) || (oldSieveChainLength < nSieveChainLength))
   {
      if (oldCandidateWords != 0)
      {
         vfComposites.clear();
      }
      vfComposites.resize(this->nSieveChainLength);
      for (unsigned int i = 0; i < nSieveChainLength; i++)
      {
         vfComposites[i].resize(this->nCandidatesWords);
         memset(&vfComposites[i][0], 0, nCandidatesBytes);
      }
   }

   if ((oldSieveChainLength < nSieveChainLength) 
      || (oldNumMultiplierRounds < nNumMultiplierRounds) 
      || (oldPrimeCount < nPrimes))
   {
      if (oldCandidateWords != 0)
      {
         vfCC1PrimeMultipliers.clear();
         vfCC2PrimeMultipliers.clear();
         vfExtendedCC1PrimesToWeave.clear();
         vfExtendedCC2PrimesToWeave.clear();
         vfCC1ExtendedPrimeCounters.clear();
         vfCC2ExtendedPrimeCounters.clear();
      }

      vfCC1PrimeMultipliers.resize(this->nSieveChainLength);
      vfCC2PrimeMultipliers.resize(this->nSieveChainLength);
      vfExtendedCC1PrimesToWeave.resize(this->nSieveChainLength);
      vfExtendedCC2PrimesToWeave.resize(this->nSieveChainLength);
      vfCC1ExtendedPrimeCounters.resize(this->nSieveChainLength);
      vfCC2ExtendedPrimeCounters.resize(this->nSieveChainLength);
      for (unsigned int i = 0; i < nSieveChainLength; i++)
      {
         vfCC1PrimeMultipliers[i].resize(this->nPrimes);
         vfCC2PrimeMultipliers[i].resize(this->nPrimes);
         vfExtendedCC1PrimesToWeave[i].resize(this->nNumMultiplierRounds);
         vfExtendedCC2PrimesToWeave[i].resize(this->nNumMultiplierRounds);
         vfCC1ExtendedPrimeCounters[i].resize(this->nNumMultiplierRounds);
         vfCC2ExtendedPrimeCounters[i].resize(this->nNumMultiplierRounds);
         for (unsigned int j = 0; j < nNumMultiplierRounds; j++)
         {
            vfExtendedCC1PrimesToWeave[i][j].resize(nPrimes / 2);
            vfExtendedCC2PrimesToWeave[i][j].resize(nPrimes / 2);
         }
      }
   }
   nPrimeMultiplierAutoWeaveCounter = 0;
   for (unsigned int i = 0; i < nSieveChainLength; i++)
   {
      memset(&vfCC1PrimeMultipliers[i][0], 0xFF, (this->nPrimes * sizeof(primeMultiplier_t)));
      memset(&vfCC2PrimeMultipliers[i][0], 0xFF, (this->nPrimes * sizeof(primeMultiplier_t)));
      memset(&vfCC1ExtendedPrimeCounters[i][0], 0, (this->nNumMultiplierRounds * sizeof(unsigned int)));
      memset(&vfCC2ExtendedPrimeCounters[i][0], 0, (this->nNumMultiplierRounds * sizeof(unsigned int)));
   }
   GenerateMultiplierTables();
}

void CSieveOfEratosthenes::GenerateMultiplierTables()
{
   const unsigned int nTotalPrimes = nPrimes;
   const unsigned int nTotalPrimesLessOne = nTotalPrimes-1;
   const unsigned int lHalfSieveSize = this->nHalfSieveSize;

   mpz_class mpzFixedFactor = mpzHash * mpzFixedMultiplier;
   mpir_ui nFixedFactorCombinedMod = 0;
   unsigned int nCombinedEndSeq = nMinPrimeSeq;

   for (unsigned int nPrimeSeq = nMinPrimeSeq; nPrimeSeq < nPrimes; nPrimeSeq++)
   {
      unsigned int nPrime = vPrimes[nPrimeSeq];
      if (nPrimeSeq >= nCombinedEndSeq)
      {
         // Combine multiple primes to produce a big divisor
         mpir_ui nPrimeCombined = 1;
         while ((nPrimeCombined < UINT_MAX / vPrimes[nCombinedEndSeq]) && (nCombinedEndSeq < nTotalPrimesLessOne))
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
      {
         error("CSieveOfEratosthenes::GenerateMultiplierTables(): int_invert of fixed factor failed for prime #%u=%u", nPrimeSeq, vPrimes[nPrimeSeq]);
         return;
      }
      unsigned int nTwoInverse = (nPrime + 1) / 2;

      // Update auto Weave prime count.
      if (nPrime < lHalfSieveSize)
      {
         nPrimeMultiplierAutoWeaveCounter = nPrimeSeq + 1;
      }

      // Weave the sieve for the prime
#ifdef _DEBUG
      unsigned int lastCC1, lastCC2;
      lastCC1 = lastCC2 = 0;
#endif
      for (unsigned int nLayerSeq = 0; nLayerSeq < nSieveChainLength; nLayerSeq++)
      {
#ifdef _DEBUG
         if ((lastCC1 > 0) && (lastCC1 % 2 == 0)) assert((lastCC1 / 2) == nFixedInverse);
         if ((lastCC2 > 0) && (lastCC2 % 2 == 0)) assert((lastCC2 / 2) == (nPrime - nFixedInverse));
         lastCC1 = nFixedInverse;
         lastCC2 = nPrime - nFixedInverse;
#endif
         // Find the first number that's divisible by this prime
         AddMultiplier(&vfCC1PrimeMultipliers[nLayerSeq], &vfExtendedCC1PrimesToWeave[nLayerSeq], &vfCC1ExtendedPrimeCounters[nLayerSeq], 0, nPrime, nPrimeSeq, nFixedInverse);
         AddMultiplier(&vfCC2PrimeMultipliers[nLayerSeq], &vfExtendedCC2PrimesToWeave[nLayerSeq], &vfCC2ExtendedPrimeCounters[nLayerSeq], 0, nPrime, nPrimeSeq, nPrime - nFixedInverse);
         // For next number in chain
         nFixedInverse = (uint64)nFixedInverse * nTwoInverse % nPrime;
      }
   }

}

void CSieveOfEratosthenes::Weave()
{
#ifdef DEBUG_SIEVE
   std::ofstream sieveLog;
   sieveLog.open("SieveDebug.log", std::ios::out | std::ios::app);
   if (sieveLog.is_open())
   {
      sieveLog << "New Weave" << std::endl;
      sieveLog.close();
   }
#endif
   primeStats.nSieveRounds++;
   primeMultiplier_t* primeMultiplier;
   const unsigned int lCurrentMultiplierRoundPos = this->nCurrentMultiplierRoundPos;
   const unsigned int lNumMultiplierRounds = this->nNumMultiplierRounds;
   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lCandidatesBytes = this->nCandidatesBytes;
   const unsigned int lSieveSize = this->nSieveSize;
   const unsigned int lRoundIncremental = 1;//(lCurrentMultiplierRoundPos == 0) ? 1: 2;
   const unsigned int multiplierPos = lCurrentMultiplierRoundPos % lNumMultiplierRounds;

   for (unsigned int layerSeq = 0; layerSeq < lSieveChainLength; layerSeq++)
   {
      memset(&vfComposites[layerSeq][0], 0, nCandidatesBytes);

      // Weave the primes that affect every bucket.
      const unsigned int numPrimeMultipliers = this->nPrimeMultiplierAutoWeaveCounter;
      for (unsigned int i = 0 ; i < numPrimeMultipliers; i++)
      {
         const unsigned int nPrime = vDoubledPrimes[i]; 
         primeMultiplier = &vfCC1PrimeMultipliers[layerSeq][i];
         if (primeMultiplier->nMultiplierCandidate == 0xFFFFFFFF) continue;
         unsigned int solvedMultiplier;
         ProcessPrimeMultiplier(&vfComposites[layerSeq], primeMultiplier, nPrime, solvedMultiplier, 0);
         primeMultiplier->nMultiplierCandidate = solvedMultiplier % lSieveSize;

         primeMultiplier = &vfCC2PrimeMultipliers[layerSeq][i];
         //if (primeMultiplier->nMultiplierCandidate == 0xFFFFFFFF) continue;
         ProcessPrimeMultiplier(&vfComposites[layerSeq], primeMultiplier, nPrime, solvedMultiplier, -1);
         primeMultiplier->nMultiplierCandidate = solvedMultiplier % lSieveSize;
      }

      // Weave the extended primes that affect the current bucket.
      const unsigned int numCC1ExtendedPrimeMultipliers = vfCC1ExtendedPrimeCounters[layerSeq][multiplierPos];
      for (unsigned int i = 0 ; i < numCC1ExtendedPrimeMultipliers; i++)
      {
         primeMultiplier = vfExtendedCC1PrimesToWeave[layerSeq][multiplierPos][i];
         const uint64 primePos = primeMultiplier - &vfCC1PrimeMultipliers[layerSeq][0];
         unsigned int solvedMultiplier;
         ProcessPrimeMultiplier(&vfComposites[layerSeq], primeMultiplier, (vPrimes[primePos] << 1), solvedMultiplier, 0);
         UpdateExtendedMultiplierList(multiplierPos, solvedMultiplier, primeMultiplier, &vfExtendedCC1PrimesToWeave[layerSeq], &vfCC1ExtendedPrimeCounters[layerSeq]);
      }
      const unsigned int numCC2ExtendedPrimeMultipliers = vfCC2ExtendedPrimeCounters[layerSeq][multiplierPos];
      for (unsigned int i = 0 ; i < numCC2ExtendedPrimeMultipliers; i++)
      {
         primeMultiplier = vfExtendedCC2PrimesToWeave[layerSeq][multiplierPos][i];
         const uint64 primePos = primeMultiplier - &vfCC2PrimeMultipliers[layerSeq][0];
         unsigned int solvedMultiplier;
         ProcessPrimeMultiplier(&vfComposites[layerSeq], primeMultiplier, (vPrimes[primePos] << 1), solvedMultiplier, -1);
         UpdateExtendedMultiplierList(multiplierPos, solvedMultiplier, primeMultiplier, &vfExtendedCC2PrimesToWeave[layerSeq], &vfCC2ExtendedPrimeCounters[layerSeq]);
      }

      // All multipliers dealt with for this round, clear layer counts.
      vfCC1ExtendedPrimeCounters[layerSeq][multiplierPos] = 0;
      vfCC2ExtendedPrimeCounters[layerSeq][multiplierPos] = 0;
   }

   // Increment current multiplier round.
   nCurrentMultiplierRoundPos += lRoundIncremental;
   nCandidateLayer = 0;
   nCandidateMultiplier = 0;
}

void CSieveOfEratosthenes::UpdateCandidateValues()
{
   memset(&vfCandidates[0], 0, nCandidatesBytes);
   memset(&vfCandidateCunningham1[0], 0, nCandidatesBytes);
   memset(&vfCandidateBiTwin[0], 0, nCandidatesBytes);

   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lCandidateLayer = this->nCandidateLayer;
   const unsigned int lCandidateWords = this->nCandidatesWords;
   const unsigned int lBTCC1ChainLength = this->nBTCC1ChainLength;
   const unsigned int lBTCC2ChainLength = this->nBTCC2ChainLength;
   const unsigned int lChainLength = this->nChainLength;//min(this->nChainLength, (lSieveChainLength - lCandidateLayer));
   for (unsigned int layerSeq = 0; layerSeq < lChainLength; layerSeq++)
   {
      const unsigned int lCompositeIndex = (layerSeq + lCandidateLayer);
      const bool fUpdateBiTwinForCC1 = (layerSeq < lBTCC1ChainLength) ? 1 : 0;
      const bool fUpdateBiTwinForCC2 = (layerSeq < lBTCC2ChainLength) ? 1 : 0;
      if (fUpdateBiTwinForCC2)// Only need to check 1 part of the BiTwin, the lesser part. If this is true, the greater part must also be true.
      {
         for (unsigned int wordNo = 0; wordNo < lCandidateWords; wordNo++)
         {
            const sieve_word_t cc1OrVal = vfComposites[lCompositeIndex][wordNo] ;
            const sieve_word_t cc2OrVal = cc1OrVal << 1;
            vfCandidateCunningham1[wordNo] |= cc1OrVal;
            vfCandidates[wordNo] |= cc2OrVal;
            vfCandidateBiTwin[wordNo] |=  cc1OrVal | cc2OrVal;
         }
      }
      else if (fUpdateBiTwinForCC1)
      {
         for (unsigned int wordNo = 0; wordNo < lCandidateWords; wordNo++)
         {
            const sieve_word_t cc1OrVal = vfComposites[lCompositeIndex][wordNo] ;
            const sieve_word_t cc2OrVal = cc1OrVal << 1;
            vfCandidateCunningham1[wordNo] |= cc1OrVal;
            vfCandidateBiTwin[wordNo] |=  cc1OrVal;
            vfCandidates[wordNo] |= cc2OrVal;
         }
      }
      else
      {
         for (unsigned int wordNo = 0; wordNo < lCandidateWords; wordNo++)
         {
            const sieve_word_t cc1OrVal = vfComposites[lCompositeIndex][wordNo] ;
            const sieve_word_t cc2OrVal = cc1OrVal << 1;
            vfCandidateCunningham1[wordNo] |= cc1OrVal;
            vfCandidates[wordNo] |= cc2OrVal;
         }
      }

   }

   // Final and.or combination
   for (unsigned int wordNo = 0; wordNo < lCandidateWords; wordNo++)
   {
      vfCandidates[wordNo] = ~(vfCandidateCunningham1[wordNo] & vfCandidates[wordNo] & vfCandidateBiTwin[wordNo]);
      vfCandidateCunningham1[wordNo] = ~(vfCandidateCunningham1[wordNo]);
      vfCandidateBiTwin[wordNo] = ~(vfCandidateBiTwin[wordNo]);
   }
   nCandidateMultiplier = 0;
   //primeStats.nCandidateCount += this->GetCandidateCount();
}

bool CSieveOfEratosthenes::GetNextCandidateMultiplier(unsigned int& nVariableMultiplier, unsigned int& nLayerMultiplier, unsigned int& nCandidateType)
{
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
         if (nCandidateLayer > nMaxCandidateLayer)
         {
            if (nCurrentMultiplierRoundPos >= this->nMaxWeaveMultiplier) return false; //(vPrimes[this->nMaxWeaveMultiplier] - 1)) return false;//1) return false; // 
            this->Weave();
         }

         // Update Candidate values
         this->UpdateCandidateValues();
         continue;
      }

#ifdef _DEBUG
      assert(nCandidateMultiplier % 2); // must be an odd number
#endif

      lWordNum = GetCandidateWordNum(nCandidateMultiplier);
      lBits = vfCandidates[lWordNum];
      if (nCandidateMultiplier % nWordBits == 1)
      {
         while (lBits == 1 && nCandidateMultiplier < nSieveSize)
         {
            // Skip an entire word
            nCandidateMultiplier += nWordBits;
            if (nCandidateMultiplier >= nSieveSize) break;
            lWordNum = GetCandidateWordNum(nCandidateMultiplier);
            lBits = vfCandidates[lWordNum];
         }
         if (nCandidateMultiplier >= nSieveSize) continue;
      }

      lBitMask = GetCompositeBitMask(nCandidateMultiplier);
      if (lBits & lBitMask)
      {
         primeStats.nCandidateCount ++;

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

void CSieveOfEratosthenes::UpdateLastCandidatePrimality(const unsigned char nCC1Composite, const unsigned char nCC2Composite)
{
   const unsigned int lCandidateLayer = (unsigned int)this->nCandidateLayer;
   const unsigned int lSieveChainLength = this->nSieveChainLength;
   const unsigned int lWordNum = GetCandidateWordNum(nCandidateMultiplier); 

   if ((nCC1Composite > 0) && ((lCandidateLayer + nCC1Composite - 1) < lSieveChainLength))
   {
      const sieve_word_t lBitMask = GetCompositeBitMask(nCandidateMultiplier);
      vfComposites[lCandidateLayer + nCC1Composite - 1][lWordNum] |= lBitMask;
   }

   if ((nCC2Composite > 0) && ((lCandidateLayer + nCC2Composite - 1) < lSieveChainLength))
   {

#ifdef _DEBUG
      const unsigned int lWordNumCC2 = GetCandidateWordNum(nCandidateMultiplier - 1); 
      assert(lWordNum == lWordNumCC2); // Must be same word despite offset..
#endif

      const sieve_word_t lBitMask = GetCompositeBitMask(nCandidateMultiplier - 1); // CC2 Composite position is offset by 1
      vfComposites[lCandidateLayer + nCC2Composite - 1][lWordNum] |= lBitMask;
   }
}
