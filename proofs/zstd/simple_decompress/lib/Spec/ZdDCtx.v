(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition DCTX_SIZEOF : Z := 95992.

Definition DCTX_LLTptr : Z := 0.   Definition DCTX_LLTptr_sz : Z := 8.
Definition DCTX_MLTptr : Z := 8.   Definition DCTX_MLTptr_sz : Z := 8.
Definition DCTX_OFTptr : Z := 16.   Definition DCTX_OFTptr_sz : Z := 8.
Definition DCTX_HUFptr : Z := 24.   Definition DCTX_HUFptr_sz : Z := 8.
Definition DCTX_entropy : Z := 32.   Definition DCTX_entropy_sz : Z := 27292.
Definition DCTX_entropy_LLTable : Z := 32.   Definition DCTX_entropy_LLTable_sz : Z := 4104.
Definition DCTX_entropy_OFTable : Z := 4136.   Definition DCTX_entropy_OFTable_sz : Z := 2056.
Definition DCTX_entropy_MLTable : Z := 6192.   Definition DCTX_entropy_MLTable_sz : Z := 4104.
Definition DCTX_entropy_hufTable : Z := 10296.   Definition DCTX_entropy_hufTable_sz : Z := 16388.
Definition DCTX_entropy_rep : Z := 26684.   Definition DCTX_entropy_rep_sz : Z := 12.
Definition DCTX_entropy_workspace : Z := 26696.   Definition DCTX_entropy_workspace_sz : Z := 628.
Definition DCTX_workspace : Z := 27324.   Definition DCTX_workspace_sz : Z := 2560.
Definition DCTX_previousDstEnd : Z := 29888.   Definition DCTX_previousDstEnd_sz : Z := 8.
Definition DCTX_prefixStart : Z := 29896.   Definition DCTX_prefixStart_sz : Z := 8.
Definition DCTX_virtualStart : Z := 29904.   Definition DCTX_virtualStart_sz : Z := 8.
Definition DCTX_dictEnd : Z := 29912.   Definition DCTX_dictEnd_sz : Z := 8.
Definition DCTX_expected : Z := 29920.   Definition DCTX_expected_sz : Z := 8.
Definition DCTX_fParams : Z := 29928.   Definition DCTX_fParams_sz : Z := 48.
Definition DCTX_processedCSize : Z := 29976.   Definition DCTX_processedCSize_sz : Z := 8.
Definition DCTX_decodedSize : Z := 29984.   Definition DCTX_decodedSize_sz : Z := 8.
Definition DCTX_bType : Z := 29992.   Definition DCTX_bType_sz : Z := 4.
Definition DCTX_stage : Z := 29996.   Definition DCTX_stage_sz : Z := 4.
Definition DCTX_litEntropy : Z := 30000.   Definition DCTX_litEntropy_sz : Z := 4.
Definition DCTX_fseEntropy : Z := 30004.   Definition DCTX_fseEntropy_sz : Z := 4.
Definition DCTX_xxhState : Z := 30008.   Definition DCTX_xxhState_sz : Z := 88.
Definition DCTX_headerSize : Z := 30096.   Definition DCTX_headerSize_sz : Z := 8.
Definition DCTX_format : Z := 30104.   Definition DCTX_format_sz : Z := 4.
Definition DCTX_forceIgnoreChecksum : Z := 30108.   Definition DCTX_forceIgnoreChecksum_sz : Z := 4.
Definition DCTX_validateChecksum : Z := 30112.   Definition DCTX_validateChecksum_sz : Z := 4.
Definition DCTX_litPtr : Z := 30120.   Definition DCTX_litPtr_sz : Z := 8.
Definition DCTX_customMem : Z := 30128.   Definition DCTX_customMem_sz : Z := 24.
Definition DCTX_litSize : Z := 30152.   Definition DCTX_litSize_sz : Z := 8.
Definition DCTX_rleSize : Z := 30160.   Definition DCTX_rleSize_sz : Z := 8.
Definition DCTX_staticSize : Z := 30168.   Definition DCTX_staticSize_sz : Z := 8.
Definition DCTX_isFrameDecompression : Z := 30176.   Definition DCTX_isFrameDecompression_sz : Z := 4.
Definition DCTX_ddictLocal : Z := 30184.   Definition DCTX_ddictLocal_sz : Z := 8.
Definition DCTX_ddict : Z := 30192.   Definition DCTX_ddict_sz : Z := 8.
Definition DCTX_dictID : Z := 30200.   Definition DCTX_dictID_sz : Z := 4.
Definition DCTX_ddictIsCold : Z := 30204.   Definition DCTX_ddictIsCold_sz : Z := 4.
Definition DCTX_dictUses : Z := 30208.   Definition DCTX_dictUses_sz : Z := 4.
Definition DCTX_ddictSet : Z := 30216.   Definition DCTX_ddictSet_sz : Z := 8.
Definition DCTX_refMultipleDDicts : Z := 30224.   Definition DCTX_refMultipleDDicts_sz : Z := 4.
Definition DCTX_disableHufAsm : Z := 30228.   Definition DCTX_disableHufAsm_sz : Z := 4.
Definition DCTX_maxBlockSizeParam : Z := 30232.   Definition DCTX_maxBlockSizeParam_sz : Z := 4.
Definition DCTX_streamStage : Z := 30236.   Definition DCTX_streamStage_sz : Z := 4.
Definition DCTX_inBuff : Z := 30240.   Definition DCTX_inBuff_sz : Z := 8.
Definition DCTX_inBuffSize : Z := 30248.   Definition DCTX_inBuffSize_sz : Z := 8.
Definition DCTX_inPos : Z := 30256.   Definition DCTX_inPos_sz : Z := 8.
Definition DCTX_maxWindowSize : Z := 30264.   Definition DCTX_maxWindowSize_sz : Z := 8.
Definition DCTX_outBuff : Z := 30272.   Definition DCTX_outBuff_sz : Z := 8.
Definition DCTX_outBuffSize : Z := 30280.   Definition DCTX_outBuffSize_sz : Z := 8.
Definition DCTX_outStart : Z := 30288.   Definition DCTX_outStart_sz : Z := 8.
Definition DCTX_outEnd : Z := 30296.   Definition DCTX_outEnd_sz : Z := 8.
Definition DCTX_lhSize : Z := 30304.   Definition DCTX_lhSize_sz : Z := 8.
Definition DCTX_hostageByte : Z := 30312.   Definition DCTX_hostageByte_sz : Z := 4.
Definition DCTX_noForwardProgress : Z := 30316.   Definition DCTX_noForwardProgress_sz : Z := 4.
Definition DCTX_outBufferMode : Z := 30320.   Definition DCTX_outBufferMode_sz : Z := 4.
Definition DCTX_expectedOutBuffer : Z := 30328.   Definition DCTX_expectedOutBuffer_sz : Z := 24.
Definition DCTX_litBuffer : Z := 30352.   Definition DCTX_litBuffer_sz : Z := 8.
Definition DCTX_litBufferEnd : Z := 30360.   Definition DCTX_litBufferEnd_sz : Z := 8.
Definition DCTX_litBufferLocation : Z := 30368.   Definition DCTX_litBufferLocation_sz : Z := 4.
Definition DCTX_litExtraBuffer : Z := 30372.   Definition DCTX_litExtraBuffer_sz : Z := 65568.
Definition DCTX_headerBuffer : Z := 95940.   Definition DCTX_headerBuffer_sz : Z := 18.
Definition DCTX_oversizedDuration : Z := 95960.   Definition DCTX_oversizedDuration_sz : Z := 8.
Definition DCTX_dictContentBeginForFuzzing : Z := 95968.   Definition DCTX_dictContentBeginForFuzzing_sz : Z := 8.
Definition DCTX_dictContentEndForFuzzing : Z := 95976.   Definition DCTX_dictContentEndForFuzzing_sz : Z := 8.
Definition DCTX_traceCtx : Z := 95984.   Definition DCTX_traceCtx_sz : Z := 8.

(* [comment removed for export] *)
Definition FH_frameContentSize : Z := 0.
Definition FH_windowSize : Z := 8.
Definition FH_blockSizeMax : Z := 16.
Definition FH_frameType : Z := 20.
Definition FH_headerSize : Z := 24.
Definition FH_dictID : Z := 28.
Definition FH_checksumFlag : Z := 32.
Definition FH_SIZEOF : Z := 48.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition WILDCOPY_OVERLENGTH : Z := 32.
Definition WILDCOPY_VECLEN : Z := 16.
Definition ZSTD_LITBUFFEREXTRASIZE : Z := 65536.      (* [comment removed for export] *)
Definition ZSTD_BLOCKSIZE_MAX : Z := 131072.
Definition MIN_CBLOCK_SIZE : Z := 2.
Definition MIN_SEQUENCES_SIZE : Z := 1.
Definition MIN_LITERALS_FOR_4_STREAMS : Z := 6.
Definition LONGNBSEQ : Z := 32512.                    (* [comment removed for export] *)
Definition ZSTD_REP_NUM : Z := 3.
Definition MINMATCH : Z := 3.
Definition MaxLL : Z := 35.
Definition MaxML : Z := 52.
Definition MaxOff : Z := 31.
Definition MaxSeq : Z := 52.
Definition LLFSELog : Z := 9.
Definition OffFSELog : Z := 8.
Definition MLFSELog : Z := 9.
Definition MaxFSELog : Z := 9.
Definition HUF_DECOMPRESS_WORKSPACE_SIZE : Z := 2560.
Definition ZSTD_BUILD_FSE_TABLE_WKSP_SIZE : Z := 626.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ZSTD_not_in_dst : Z := 0.
Definition ZSTD_in_dst : Z := 1.
Definition ZSTD_split : Z := 2.
(* [comment removed for export] *)
Definition set_basic : Z := 0.
Definition set_rle : Z := 1.
Definition set_compressed : Z := 2.
Definition set_repeat : Z := 3.

(* [comment removed for export] *)
Lemma DCTX_layout_facts :
  DCTX_entropy_LLTable = DCTX_entropy /\
  DCTX_entropy_OFTable = DCTX_entropy_LLTable + 8 * (1 + 2^9) /\
  DCTX_entropy_MLTable = DCTX_entropy_OFTable + 8 * (1 + 2^8) /\
  DCTX_entropy_hufTable = DCTX_entropy_MLTable + 8 * (1 + 2^9) /\
  DCTX_entropy_rep = DCTX_entropy_hufTable + 4 * (1 + 2^12) /\
  DCTX_litExtraBuffer_sz = ZSTD_LITBUFFEREXTRASIZE + WILDCOPY_OVERLENGTH /\
  DCTX_traceCtx + DCTX_traceCtx_sz = DCTX_SIZEOF.
Proof. repeat split. Qed.
