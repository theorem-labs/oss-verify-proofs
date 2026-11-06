(* reac-pw/fuzz_link, PLAIN build: the two statements that turn link's memory FILE as the contracts
   state it (lib/Prog/memfile_c.v: memfile_k, mf_dyn, mf_pend_bytes; lib/MemFile.v memfile_at) into the
   FILE as vfprintf's walk reads it (the 232 bytes as cells, lib/Prog/mf_sink_c.v `mf_file`), and back.

   `mf_file_l` is `mf_sink_c.mf_file` over lib/Lib's cells (CJBridge.cell_to maps one onto the other).
   - `mf_cells_of_k_stmt`: before the call, the FILE's bytes as cells (the bytes vfprintf does not read
     kept as they are), the buffer as the k pending bytes then the rest, the window, F_NOWR clear and the
     orientation 0 or -1.
   - `mf_post_of_cells_stmt`: after the call, if the 232 bytes are the same cells with the window active
     and k + |T| bytes pending, the buffer holds the pending bytes then T, and nothing else of the block
     changed (the cookie at +232 and the bytes up to the buffer), then `pf_file_post` holds. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c vfprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI14.
Local Open Scope Z_scope.

Definition mf_file_l (fl : word) (jp jc : list byte) (we wp : word) (j48 : list byte) (wb : word) (j64 : list byte)
    (buf : Z) (j104 : list byte) (mode lbf : word) (jx : list byte) : list cell :=
  [C4 fl; CB 4 jp; C8 (wz 0); C8 (wz 0); CB 8 jc; C8 we; C8 wp; CB 8 j48; C8 wb; CB 24 j64;
   C8 (wz buf); C8 (wz 1024); CB 32 j104; C4 mode; C4 (wz (-1)); C4 lbf; CB 84 jx].

Definition mf_cells_of_k_stmt : Prop :=
  forall (m : word -> option byte) (f k fl om wend wpos wbase pos len : Z) (pb : list byte),
    memfile_k m f k -> mf_dyn m f fl om wend wpos wbase pos len -> mf_pend_bytes m f pb ->
    Z.of_nat (length pb) = k ->
    exists (jp jc j48 j64 j104 jx bjunk : list byte),
      rw_cells rsegs m f
        (mf_file_l (wz fl) jp jc (wz wend) (wz wpos) j48 (wz wbase) j64 (f + MemFile.MF_BUF) j104 (wz om)
                   (wz YI14.U32M1) jx) /\
      rw_cells rsegs m (f + MemFile.MF_BUF) [CB (length pb) pb; CB (length bjunk) bjunk] /\
      Z.of_nat (length pb) + Z.of_nat (length bjunk) = MemFile.MF_BUFSIZ /\
      ((wend = 0 /\ k = 0) \/
       (wend = f + MemFile.MF_BUF + MemFile.MF_BUFSIZ /\ wpos = f + MemFile.MF_BUF + k /\ wbase = f + MemFile.MF_BUF)) /\
      Z.land fl 8 = 0 /\ (om = 0 \/ om = YI14.U32M1).

Definition mf_post_of_cells_stmt : Prop :=
  forall (m m' : word -> option byte) (f k fl om wend wpos wbase pos len lo sp : Z) (pb : list byte) (T : list Z)
         (jp jc j48 j64 j104 jx bj : list byte),
    memfile_k m f k -> mf_dyn m f fl om wend wpos wbase pos len -> Z.of_nat (length pb) = k ->
    rw_cells rsegs m f
      (mf_file_l (wz fl) jp jc (wz wend) (wz wpos) j48 (wz wbase) j64 (f + MemFile.MF_BUF) j104 (wz om)
                 (wz YI14.U32M1) jx) ->
    munch [(lo, sp); (f, f + 232); (f + MemFile.MF_BUF, f + MemFile.MF_BLOCK)] m m' ->
    f + MemFile.MF_BLOCK <= lo -> f + MemFile.MF_BLOCK < 2 ^ 63 -> wmono rsegs m m' ->
    rw_cells rsegs m' f
      (mf_file_l (wz fl) jp jc (wz (f + MemFile.MF_BUF + MemFile.MF_BUFSIZ))
                 (wz (f + MemFile.MF_BUF + k + Z.of_nat (length T))) j48 (wz (f + MemFile.MF_BUF)) j64
                 (f + MemFile.MF_BUF) j104 (wz (if wend =? 0 then YI14.U32M1 else om)) (wz YI14.U32M1) jx) ->
    rw_cells rsegs m' (f + MemFile.MF_BUF) [CB (length (pb ++ pf_bytes T)) (pb ++ pf_bytes T); CB (length bj) bj] ->
    k + Z.of_nat (length T) <= MemFile.MF_BUFSIZ ->
    pf_file_post m' f k pb T fl om wend pos len.
