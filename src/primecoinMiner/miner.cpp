#include"global.h"
#include <time.h>


bool MineProbablePrimeChain(CSieveOfEratosthenes*& psieve, primecoinBlock_t* block, mpz_class& bnFixedMultiplier, bool& fNewBlock, 
                            sint32 threadIndex, mpz_class& mpzHash, unsigned int nPrimorialMultiplier);

std::set<mpz_class> multiplierSet;

bool BitcoinMiner(primecoinBlock_t* primecoinBlock, CSieveOfEratosthenes*& psieve, const sint32 threadIndex, const unsigned int nonceStep)
{
   //printf("PrimecoinMiner started\n");
   //SetThreadPriority(THREAD_PRIORITY_LOWEST);
   //RenameThread("primecoin-miner");
   if( pctx == NULL )
      pctx = BN_CTX_new();
   // Each thread has its own key and counter
   //CReserveKey reservekey(pwallet);
   unsigned int nExtraNonce = 0;

   static const unsigned int MAX_NONCE = 0xFFFF0000; // From Primecoind sources.
   static const unsigned int nPrimorialHashFactor = 7;

   int64 nTimeExpected = 0;   // time expected to prime chain (micro-second)
   int64 nTimeExpectedPrev = 0; // time expected to prime chain last time
   bool fIncrementPrimorial = true; // increase or decrease primorial factor
   int64 nSieveGenTime = 0;

   // Generate a thread specific nonce.
   primecoinBlock->nonce = threadIndex;

   uint32 nTime = GetTickCount() + 1000*600;
   uint32 nStatTime = GetTickCount() + 2000;

   unsigned int nHashFactor = PrimorialFast(nPrimorialHashFactor);
   unsigned int nPrimorialMultiplier = primeStats.nPrimorialMultiplier;
   mpz_class mpzPrimorial;
   Primorial(nPrimorialMultiplier, mpzPrimorial);
   mpz_class mpzFixedMultiplier;
   if (primecoinBlock->miningVersion >= 2)
   {
      mpzFixedMultiplier = mpzPrimorial;
   }
   else
   {
      if (mpzPrimorial > nHashFactor) {
         mpzFixedMultiplier = mpzPrimorial / nHashFactor;
      } else {
         mpzFixedMultiplier = 1;
      }		
   }

   time_t unixTimeStart;
   time(&unixTimeStart);
   uint32 nTimeRollStart = primecoinBlock->timestamp - 5;
   uint32 nLastRollTime = GetTickCount();
   uint32 nCurrentTick = nLastRollTime;
   while( nCurrentTick < nTime && primecoinBlock->serverData.blockHeight == jhMiner_getCurrentWorkBlockHeight(primecoinBlock->threadIndex) )
   {
      nCurrentTick = GetTickCount();
      // Roll Time stamp every 10 secs.
      if ((primecoinBlock->xptMode) && (nCurrentTick < nLastRollTime || (nLastRollTime - nCurrentTick >= 10000)))
      {
         // when using x.pushthrough, roll time
         time_t unixTimeCurrent;
         time(&unixTimeCurrent);
         uint32 timeDif = unixTimeCurrent - unixTimeStart;
         uint32 newTimestamp = nTimeRollStart + timeDif;
         if( newTimestamp != primecoinBlock->timestamp )
         {
            primecoinBlock->timestamp = newTimestamp;
            primecoinBlock->nonce = threadIndex;
         }
         nLastRollTime = nCurrentTick;
      }

      //
      // Search
      //
      bool fNewBlock = true;
      // Primecoin: try to find hash divisible by primorial
      mpz_class mpzHash;
      while (true)
      {
         primecoinBlock->nonce += nonceStep;
         if (primecoinBlock->nonce >= MAX_NONCE) 
            break;

         // Verify the block hash is valid
         primecoinBlock_generateHeaderHash(primecoinBlock, primecoinBlock->blockHeaderHash.begin());
         uint256 phash = primecoinBlock->blockHeaderHash;
         if (phash < hashBlockHeaderLimit) 
            continue;

         // Test hash is usable.
         mpz_set_uint256(mpzHash.get_mpz_t(), phash);
         if (primecoinBlock->miningVersion >= 2)
         {
            // Try to find hash that is probable prime
            if (!ProbablePrimalityTestWithTrialDivision(mpzHash, 1000))
               continue;
         } else {
            // Primecoin: Check that the hash is divisible by the fixed primorial
            if (!mpz_divisible_ui_p(mpzHash.get_mpz_t(), nHashFactor))
               continue;
         }

         // Hash has passed required tests, use it.
         break;
      }
      //printf("Use nonce %d\n", primecoinBlock->nonce);
      if (primecoinBlock->nonce >= MAX_NONCE)
      {
         break;
      }

      // Primecoin: mine for prime chain
      MineProbablePrimeChain(psieve, primecoinBlock, mpzFixedMultiplier, fNewBlock, threadIndex, mpzHash, nPrimorialMultiplier);
      threadHearthBeat[threadIndex] = GetTickCount();
      if (appQuitSignal)
      {
         printf( "Shutting down mining thread %d.\n", threadIndex);
         return false;
      }
   }

   return true;
}
