#ifndef PRIMECOIN_SIEVE_H
#define PRIMECOIN_SIEVE_H

#include "mpirxx.h"
//
extern uint32 vPrimesSize;
extern std::vector<unsigned int> vPrimes;

#ifdef _M_X64
typedef uint64 sieve_word_t;
#else
typedef unsigned long sieve_word_t;
#endif

typedef struct
{
   unsigned int nMultiplierBits; // 32 bit integer containing:11 bits for Layer number, 1 bit for CC2 indicator, 20 bits for Prime index. 
   unsigned int nMultiplierCandidate;
}primeMultiplier_t;

class CSieveOfEratosthenes
{
   static const unsigned int nWordBits = 8 * sizeof(sieve_word_t);	
   static const int nMinPrimeSeq = 4; // this is Prime number 11, the first prime with unknown factor status.
   static const int nMaxWeaveMultiplier = 8; // This is the 9th prime (23) which will be the maximum number of individual weaves.
   unsigned int nSieveSize; // size of the sieve
   unsigned int nSievePercentage;
   unsigned int nSieveExtension;
   unsigned int nChainLength;
   unsigned int nBTCC1ChainLength;
   unsigned int nBTCC2ChainLength;
   unsigned int nSieveChainLength;
   unsigned int nPrimes;
   unsigned int nPrimesDoubled;
   unsigned int nNumMultiplierRounds;
   unsigned int nCurrentMultiplierRoundPos;
   unsigned int nCurrentWeaveMultiplier;

   mpz_class mpzHash; // hash of the block header
   mpz_class mpzFixedMultiplier; // fixed round multiplier

   unsigned int nCandidatesWords;
   unsigned int nCandidatesBytes;
   unsigned int nCandidateMultiplier; // current candidate for power test
   unsigned int nCandidateLayer;

   // final set of candidates for probable primality checking
   sieve_word_t* vfCandidates;
   sieve_word_t* vfCandidateBiTwin;
   sieve_word_t* vfCandidateCunningham1;

   // bitsets that can be combined to obtain the final bitset of candidates
   sieve_word_t* vfCompositeCunningham1;
   sieve_word_t* vfCompositeCunningham2;

   // multipliers split into sieve segments.
   primeMultiplier_t* vfPrimeMultipliers;
   unsigned int* vfPrimeMultiplierCounts;

   unsigned int GetCandidateWordNum(unsigned int nBitNum) {
      return nBitNum / nWordBits;
   }

   sieve_word_t  GetCompositeBitMask(unsigned int nBitNum) {
      return (sieve_word_t)1UL << (nBitNum % nWordBits);
   }
/*
   __inline void AddMultiplier(unsigned int *vMultipliers, const unsigned int nArrayOffset, const unsigned int nMultiplierPos, const unsigned int nPrimeSeq, const unsigned int nSolvedMultiplier);


   void ProcessMultiplier(uint64 *vfComposites,const unsigned int nArrayOffset, const unsigned int nMinMultiplier, const unsigned int nMaxMultiplier, const std::vector<unsigned int>& vPrimes, unsigned int *vMultipliers)
   {
      // Wipe the part of the array first
      memset(vfComposites + GetWordNum(nMinMultiplier), 0, (nMaxMultiplier - nMinMultiplier + nWordBits - 1) / nWordBits * sizeof(uint64));
      int multiplierPos = (nMinPrimeSeq * nArrayOffset) -1;
      for (unsigned int nPrimeSeq = nMinPrimeSeq; nPrimeSeq < nPrimes; nPrimeSeq++)
      {
         const unsigned int nPrime = vPrimes[nPrimeSeq];
#ifdef USE_ROTATE
         const unsigned int nRotateBits = nPrime % nWordBits;
         for (unsigned int i = 0; i < nArrayOffset; i++)
         {
            unsigned int nVariableMultiplier = vMultipliers[nPrimeSeq * nArrayOffset + i];
            if (nVariableMultiplier == 0xFFFFFFFF) continue;
            unsigned long lBitMask = GetBitMask(nVariableMultiplier);
            while (nVariableMultiplier < nMaxMultiplier)
            {
               vfComposites[GetWordNum(nVariableMultiplier)] |= lBitMask;
               lBitMask = (lBitMask << nRotateBits) | (lBitMask >> (nWordBits - nRotateBits));
               nVariableMultiplier += nPrime;
            }
            vMultipliers[nPrimeSeq * nArrayOffset + i] = nVariableMultiplier;
         }
#else
         for (unsigned int i = 0; i < nArrayOffset; i++)
         {
            multiplierPos++;
            //unsigned int nVariableMultiplier = vMultipliers[nPrimeSeq * nArrayOffset + i];
            unsigned int nVariableMultiplier = vMultipliers[multiplierPos];
            //if (nVariableMultiplier == 0xFFFFFFFF) continue;
            while (nVariableMultiplier < nMaxMultiplier)
            {
               vfComposites[GetWordNum(nVariableMultiplier)] |= GetBitMask(nVariableMultiplier);
               nVariableMultiplier += nPrime;
            }
            //vMultipliers[nPrimeSeq * nArrayOffset + i] = nVariableMultiplier;
            vMultipliers[multiplierPos] = nVariableMultiplier;
         }
#endif
      }
   }
*/

   //_inline unsigned int GetPrimeMultiplierPosition(const unsigned int currentMultiplierRound, const unsigned int solvedMultiplier

   unsigned int GetPrimeMultiplierItemPosition(const unsigned int multiplierPos, const unsigned int layerSeq, const unsigned int itemPosition)
   {
      const unsigned int lSieveChainLength = this->nSieveChainLength;
      const unsigned int lPrimesDoubled = this->nPrimesDoubled;
      return (multiplierPos * lPrimesDoubled * lSieveChainLength) + (lPrimesDoubled * layerSeq) + itemPosition;
   }

   unsigned int GetPrimeMultiplierCountPosition(const unsigned int multiplierPos, const unsigned int layerSeq)
   {
      const unsigned int lSieveChainLength = this->nSieveChainLength;
      return (multiplierPos * lSieveChainLength) + layerSeq;
   }

   void AddMultiplierWithBits(const unsigned int nCurrentMuliplierRound, const unsigned int nLayerNum, const unsigned int nMultiplierBits, const unsigned int nSolvedMultiplier);

   void AddMultiplier(const unsigned int nCurrentMuliplierRound, const unsigned int nLayerNum, const bool isCunninghamChain1, const unsigned int nPrimeSeq, const unsigned int nSolvedMultiplier);

   bool GenerateMultiplierTables();

   void Weave();

   void UpdateCandidateValues();


public:

   CSieveOfEratosthenes(unsigned int sieveSize, unsigned int sievePercentage, unsigned int nSieveExtension, unsigned int targetChainLength, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier)
   {
      this->nCandidatesWords = 0;
      this->nSieveChainLength = 0;
      this->nPrimes = 0;
      this->nNumMultiplierRounds = 0;
      Init(sieveSize, sievePercentage, nSieveExtension, targetChainLength, mpzHash, mpzFixedMultiplier);
   }

   ~CSieveOfEratosthenes(void);

   void Init(unsigned int nSieveSize, unsigned int nSievePercentage, unsigned int nSieveExtension, unsigned int nTargetChainLength, mpz_class& mpzHash, mpz_class& mpzFixedMultiplier);

   bool GetNextCandidateMultiplier(unsigned int& nVariableMultiplier, unsigned int& nLayerMultiplier, unsigned int& nCandidateType);

//
   // Get total number of candidates for power test
   unsigned int GetCandidateCount()
   {
      unsigned int nCandidates = 0;
#ifdef __GNUC__
      for (unsigned int i = 0; i < nCandidatesWords; i++)
      {
         nCandidates += __builtin_popcountl(vfCandidates[i]);
      }
#else
      for (unsigned int i = 0; i < nCandidatesWords; i++)
      {
         sieve_word_t lBits = vfCandidates[i];
         for (unsigned int j = 0; j < nWordBits; j++)
         {
            nCandidates += (lBits & 1UL);
            lBits >>= 1;
         }
      }
#endif
      return nCandidates;
   }
//
//   // Scan for the next candidate multiplier (variable part)
//   // Return values:
//   //   True - found next candidate; nVariableMultiplier has the candidate
//   //   False - scan complete, no more candidate and reset scan
//   bool GetNextCandidateMultiplier(unsigned int& nVariableMultiplier, unsigned int& nCandidateType)
//   {
///*      unsigned int lWordNum = GetWordNum(nCandidateMultiplier);
//
//      uint64 lBits = vfCandidates[lWordNum];
//      uint64 lBitMask;
//
//      for(;;)
//      {
//         nCandidateMultiplier++;
//         if (nCandidateMultiplier >= nSieveSize)
//         {
//            nCandidateMultiplier = 0;
//            return false;
//         }
//         if (nCandidateMultiplier % nWordBits == 0)
//         {
//            lWordNum = GetWordNum(nCandidateMultiplier);
//            lBits = vfCandidates[lWordNum];
//            if (lBits == 0)
//            {
//               // Skip an entire word
//               nCandidateMultiplier += nWordBits - 1;
//               continue;
//            }
//         }
//         lBitMask = GetBitMask(nCandidateMultiplier);
//         if (lBits & lBitMask)
//         {
//
//            nVariableMultiplier = nCandidateMultiplier;
//            if (vfCandidateBiTwin[GetWordNum(nCandidateMultiplier)] & GetBitMask(nCandidateMultiplier))
//               nCandidateType = PRIME_CHAIN_BI_TWIN;
//            else if (vfCandidateCunningham1[GetWordNum(nCandidateMultiplier)] & GetBitMask(nCandidateMultiplier))
//               nCandidateType = PRIME_CHAIN_CUNNINGHAM1;
//            else
//               nCandidateType = PRIME_CHAIN_CUNNINGHAM2;
//            return true;
//         }
//      }
//      */
//      return true;
//   }
//
//   void SetSievePercentage(unsigned int newSievePercentage)
//   {
//      this->nSievePercentage = newSievePercentage;
//      this->nPrimes = (uint64)vPrimesSize * nSievePercentage / 100;
//   }
};


#endif