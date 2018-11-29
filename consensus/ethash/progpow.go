package ethash

import (
	"encoding/binary"
	"github.com/ethereum/go-ethereum/crypto/sha3"
)

const (
	progpowCacheBytes = 16 * 1024             // Total size 16*1024 bytes
	progpowCacheWords = progpowCacheBytes / 4 // Total size 16*1024 bytes
	progpowLanes      = 16
	progpowRegs       = 32
	progpowCntCache   = 12
	progpowCntMath    = 20
	progpowDagLoads   = 4
	progpowCntDag     = 64
	progpowMixBytes   = 2 * mixBytes
	progpowPeriod     = 50
)

func progpowLight(size uint64, cache []uint32, hash []byte, nonce uint64,
	blockNumber uint64, cDag []uint32) ([]byte, []byte) {
	keccak512 := makeHasher(sha3.NewKeccak512())

	lookup := func(index uint32) []byte {
		rawData := generateDatasetItem(cache, index/16, keccak512)
		return rawData
	}
	return progpow(hash, nonce, size, blockNumber, cDag, lookup)
}

func progpowFull(dataset []uint32, hash []byte, nonce uint64,
	blockNumber uint64) ([]byte, []byte) {

	lookup := func(index uint32) []byte {
		mix := make([]byte, hashBytes)

		for i := uint32(0); i < hashWords; i++ {
			binary.LittleEndian.PutUint32(mix[i*4:], dataset[(index/16)*16+i])
		}
		return mix
	}

	cDag := make([]uint32, progpowCacheWords)

	// initialize cDag
	for i := uint32(0); i < progpowCacheWords; i++ {
		cDag[i] = dataset[i]
	}

	return progpow(hash, nonce, uint64(len(dataset))*4, blockNumber, cDag, lookup)
}

func rotl32(x uint32, n uint32) uint32 {
	return (((x) << (n % 32)) | ((x) >> (32 - (n % 32))))
}

func rotr32(x uint32, n uint32) uint32 {
	return (((x) >> (n % 32)) | ((x) << (32 - (n % 32))))
}

func lower32(in uint64) uint32 {
	return uint32(in & uint64(0x00000000FFFFFFFF))
}

func higher32(in uint64) uint32 {
	return uint32((in >> 32) & uint64(0x00000000FFFFFFFF))
}

var keccakfRNDC = [24]uint32{
	0x00000001, 0x00008082, 0x0000808a, 0x80008000, 0x0000808b, 0x80000001,
	0x80008081, 0x00008009, 0x0000008a, 0x00000088, 0x80008009, 0x8000000a,
	0x8000808b, 0x0000008b, 0x00008089, 0x00008003, 0x00008002, 0x00000080,
	0x0000800a, 0x8000000a, 0x80008081, 0x00008080, 0x80000001, 0x80008008}

func keccakF800Round(st [25]uint32, r int) [25]uint32 {
	var keccakfROTC = [24]uint32{1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2,
		14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61,
		20, 44}
	var keccakfPILN = [24]uint32{10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24,
		4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9,
		6, 1}
	bc := make([]uint32, 5)
	// Theta
	for i := 0; i < 5; i++ {
		bc[i] = st[i] ^ st[i+5] ^ st[i+10] ^ st[i+15] ^ st[i+20]
	}

	for i := 0; i < 5; i++ {
		t := bc[(i+4)%5] ^ rotl32(bc[(i+1)%5], 1)
		for j := 0; j < 25; j += 5 {
			st[j+i] ^= t
		}
	}

	// Rho Pi
	t := st[1]
	for i := 0; i < 24; i++ {
		j := keccakfPILN[i]
		bc[0] = st[j]
		st[j] = rotl32(t, keccakfROTC[i])
		t = bc[0]
	}

	//  Chi
	for j := 0; j < 25; j += 5 {
		for i := 0; i < 5; i++ {
			bc[i] = st[j+i]
		}
		for i := 0; i < 5; i++ {
			st[j+i] ^= (^bc[(i+1)%5]) & bc[(i+2)%5]
		}
	}

	//  Iota
	st[0] ^= keccakfRNDC[r]
	return st
}

func byteReverse(i uint32) uint32 {
	var ret uint32

	ret = 0
	ret += (i & 0xFF)
	ret <<= 8
	ret += ((i >> 8) & 0xFF)
	ret <<= 8
	ret += ((i >> 16) & 0xFF)
	ret <<= 8
	ret += (i >> 24)

	return ret
}

func keccakF800(headerHash []byte, nonce uint64, result []uint32) uint64 {
	var st [25]uint32
	var ret uint64

	for i := 0; i < 25; i++ {
		st[i] = 0
	}

	for i := 0; i < 8; i++ {
		st[i] = (uint32(headerHash[4*i])) +
			(uint32(headerHash[4*i+1]) << 8) +
			(uint32(headerHash[4*i+2]) << 16) +
			(uint32(headerHash[4*i+3]) << 24)
	}

	st[8] = lower32(nonce)
	st[9] = higher32(nonce)
	for i := 0; i < 8; i++ {
		st[10+i] = result[i]
	}
	for r := 0; r < 21; r++ {
		st = keccakF800Round(st, r)
	}
	st = keccakF800Round(st, 21)
	ret = uint64(byteReverse(st[0]))
	ret = (ret << 32) + uint64(byteReverse(st[1]))
	return ret
}

func keccakF800Full(headerHash []byte, nonce uint64, result []uint32) []byte {
	var st [25]uint32

	for i := 0; i < 25; i++ {
		st[i] = 0
	}
	for i := 0; i < 8; i++ {
		st[i] = (uint32(headerHash[4*i])) +
			(uint32(headerHash[4*i+1]) << 8) +
			(uint32(headerHash[4*i+2]) << 16) +
			(uint32(headerHash[4*i+3]) << 24)
	}

	st[8] = lower32(nonce)
	st[9] = higher32(nonce)
	for i := 0; i < 8; i++ {
		st[10+i] = result[i]
	}
	for r := 0; r < 21; r++ {
		st = keccakF800Round(st, r)
	}
	st = keccakF800Round(st, 21)
	ret := make([]byte, 32)
	for i := 0; i < 8; i++ {
		binary.LittleEndian.PutUint32(ret[i*4:], st[i])
	}
	return ret
}

func fnv1a(h *uint32, d uint32) uint32 {
	*h = (*h ^ d) * uint32(0x1000193)
	return *h
}

type kiss99State struct {
	z     uint32
	w     uint32
	jsr   uint32
	jcong uint32
}

func kiss99(st *kiss99State) uint32 {
	var MWC uint32
	st.z = 36969*(st.z&65535) + (st.z >> 16)
	st.w = 18000*(st.w&65535) + (st.w >> 16)
	MWC = ((st.z << 16) + st.w)
	st.jsr ^= (st.jsr << 17)
	st.jsr ^= (st.jsr >> 13)
	st.jsr ^= (st.jsr << 5)
	st.jcong = 69069*st.jcong + 1234567
	return ((MWC ^ st.jcong) + st.jsr)
}

func fillMix(seed uint64, laneId uint32) [progpowRegs]uint32 {
	var st kiss99State
	var mix [progpowRegs]uint32

	fnvHash := uint32(0x811c9dc5)

	st.z = fnv1a(&fnvHash, lower32(seed))
	st.w = fnv1a(&fnvHash, higher32(seed))
	st.jsr = fnv1a(&fnvHash, laneId)
	st.jcong = fnv1a(&fnvHash, laneId)

	for i := 0; i < progpowRegs; i++ {
		mix[i] = kiss99(&st)
	}
	return mix
}

func clz(a uint32) uint32 {
	for i := uint32(0); i < 32; i++ {
		if (a >> (31 - i)) > 0 {
			return i
		}
	}
	return uint32(32)
}

func popcount(a uint32) uint32 {
	count := uint32(0)
	for i := uint32(0); i < 32; i++ {
		if ((a >> (31 - i)) & uint32(1)) == uint32(1) {
			count += 1
		}
	}
	return count
}

// Merge new data from b into the value in a
// Assuming A has high entropy only do ops that retain entropy
// even if B is low entropy
// (IE don't do A&B)
func merge(a *uint32, b uint32, r uint32) {
	switch r % 4 {
	case 0:
		*a = (*a * 33) + b
	case 1:
		*a = (*a ^ b) * 33
	case 2:
		*a = rotl32(*a, ((r>>16)%32)) ^ b
	case 3:
		*a = rotr32(*a, ((r>>16)%32)) ^ b
	}
}

func progpowInit(blockNumberRounded uint64) (kiss99State, [progpowRegs]uint32,
	[progpowRegs]uint32) {
	var seed uint64
	var randState kiss99State
	var mixSeqDest [progpowRegs]uint32
	var mixSeqCache [progpowRegs]uint32

	seed = blockNumberRounded / progpowPeriod

	fnvHash := uint32(0x811c9dc5)

	randState.z = fnv1a(&fnvHash, lower32(seed))
	randState.w = fnv1a(&fnvHash, higher32(seed))
	randState.jsr = fnv1a(&fnvHash, lower32(seed))
	randState.jcong = fnv1a(&fnvHash, higher32(seed))

	// Create a random sequence of mix destinations for merge()
	// guaranteeing every location is touched once
	// Uses Fisher CYates shuffle
	for i := uint32(0); i < progpowRegs; i++ {
		mixSeqDest[i] = i
		mixSeqCache[i] = i
	}

	for i := uint32(progpowRegs - 1); i > 0; i-- {
		var j, temp uint32

		j = kiss99(&randState) % (i + 1)
		temp = mixSeqDest[i]
		mixSeqDest[i] = mixSeqDest[j]
		mixSeqDest[j] = temp

		j = kiss99(&randState) % (i + 1)
		temp = mixSeqCache[i]
		mixSeqCache[i] = mixSeqCache[j]
		mixSeqCache[j] = temp
	}
	return randState, mixSeqDest, mixSeqCache
}

// Random math between two input values
func progpowMath(a uint32, b uint32, r uint32) uint32 {
	switch r % 11 {
	case 0:
		return a + b
	case 1:
		return a * b
	case 2:
		return higher32(uint64(a) * uint64(b))
	case 3:
		if a < b {
			return a
		}
		return b
	case 4:
		return rotl32(a, b)
	case 5:
		return rotr32(a, b)
	case 6:
		return a & b
	case 7:
		return a | b
	case 8:
		return a ^ b
	case 9:
		return clz(a) + clz(b)
	case 10:
		return popcount(a) + popcount(b)
	default:
		return 0
	}
}

func progpowLoop(seed uint64, loop uint32,
	mix *[progpowLanes][progpowRegs]uint32,
	lookup func(index uint32) []byte,
	cDag []uint32, datasetSize uint32) {

	var dagData [4]uint32
	// All lanes share a base address for the global load
	// Global offset uses mix[0] to guarantee it depends on the load result
	gOffset := mix[loop%progpowLanes][0] % datasetSize
	gOffset = gOffset * progpowLanes
	iMax := uint32(0)

	// Index of last read from DAG. Needed to reduce number of DAG loads
	gIndex := uint32(0)
	rawDagData := make([]byte, hashBytes)
	// Lanes can execute in parallel and will be convergent
	for lane := uint32(0); lane < progpowLanes; lane++ {
		mixSeqCacheCnt := uint32(0)
		mixSeqDestCnt := uint32(0)

		gOffsetLane := gOffset + ((lane ^ loop) % progpowLanes)
		if lane == uint32(0) || gIndex != (gOffsetLane*4)/16 {
			gIndex = (gOffsetLane * 4) / 16
			rawDagData = lookup(gOffsetLane * 4)
		}
		for i := uint32(0); i < 4; i++ {
			// global load to sequential locations
			dagData[i] = binary.LittleEndian.Uint32(rawDagData[((gOffsetLane*4+i)%16)*4:])
		}

		// initialize the seed and mix destination sequence
		randState, mixSeqDest, mixSeqCache := progpowInit(seed)

		if progpowCntCache > progpowCntMath {
			iMax = progpowCntCache
		} else {
			iMax = progpowCntMath
		}

		for i := uint32(0); i < iMax; i++ {
			if i < progpowCntCache {
				// Cached memory access
				// lanes access random location
				src := mixSeqCache[mixSeqCacheCnt%progpowRegs]
				mixSeqCacheCnt++
				offset := mix[lane][src] % progpowCacheWords
				data32 := cDag[offset]
				dest := mixSeqDest[mixSeqDestCnt%progpowRegs]
				mixSeqDestCnt++
				r := kiss99(&randState)
				merge(&mix[lane][dest], data32, r)
			}

			if i < progpowCntMath {
				// Random Math
				src1 := kiss99(&randState) % progpowRegs
				src2 := kiss99(&randState) % progpowRegs
				r1 := kiss99(&randState)
				dest := mixSeqDest[mixSeqDestCnt%progpowRegs]
				mixSeqDestCnt++
				r2 := kiss99(&randState)
				data32 := progpowMath(mix[lane][src1], mix[lane][src2], r1)
				merge(&mix[lane][dest], data32, r2)
			}
		}

		r := kiss99(&randState)
		merge(&mix[lane][0], dagData[0], r)
		for i := uint32(1); i < progpowDagLoads; i++ {
			dest := mixSeqDest[mixSeqDestCnt%progpowRegs]
			mixSeqDestCnt++
			r := kiss99(&randState)
			merge(&mix[lane][dest], dagData[i], r)
		}
	}
}

func progpow(hash []byte, nonce uint64, size uint64, blockNumber uint64, cDag []uint32,
	lookup func(index uint32) []byte) ([]byte, []byte) {
	var mix [progpowLanes][progpowRegs]uint32
	var laneDigest [progpowLanes]uint32

	digest := make([]uint32, 8)

	for i := uint32(0); i < 8; i++ {
		digest[i] = 0
	}

	seed := keccakF800(hash, nonce, digest)
	for lane := uint32(0); lane < progpowLanes; lane++ {
		mix[lane] = fillMix(seed, lane)
	}

	blockNumberRounded := (blockNumber / epochLength) * epochLength
	for loop := uint32(0); loop < progpowCntDag; loop++ {
		progpowLoop(blockNumberRounded, loop, &mix, lookup, cDag,
			uint32(size/progpowMixBytes))
	}

	// Reduce mix data to a single per-lane result
	for lane := uint32(0); lane < progpowLanes; lane++ {
		laneDigest[lane] = 0x811c9dc5
		for i := uint32(0); i < progpowRegs; i++ {
			fnv1a(&laneDigest[lane], mix[lane][i])
		}
	}

	for i := uint32(0); i < 8; i++ {
		digest[i] = 0x811c9dc5
	}
	for lane := uint32(0); lane < progpowLanes; lane++ {
		fnv1a(&digest[lane%8], laneDigest[lane])
	}

	result := keccakF800Full(hash, seed, digest[:])

	digestBytes := make([]byte, 8*4)
	for i := 0; i < 8; i++ {
		binary.LittleEndian.PutUint32(digestBytes[i*4:], digest[i])
	}

	return digestBytes[:], result[:]
}
