(* SCRATCH (a Theorem Labs lane R6): put_string's CLOSING THEOREM, as four segments and their glue.
   `ps_inv` is the bundle the walk carries at each put call's RETURN. The four segment statements are the
   explicit premises of ps_close, so each part proves one of them as a Lemma in its own file and the fold
   instantiates ps_close with the four. Folded into FSW_put_string.v once every piece is Qed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame
FSW_frame3 FSW_writer_tbl FSW_writer_model FSW_put_string ZZpsjoin.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
Import ListNotations.
Open Scope Z_scope.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the model state after the first `ps` pieces *)
Definition ps_st (failed : Z) (text : list Z) (cap cnt fail : Z) (ps : list (list Z)) : WriterApp.wst :=
  WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) ps.

(* ---- put_string_spec's premises, bundled. The spec gives them curried; ps_close rebundles them once so that
   the four segments each take one hypothesis instead of twenty-six. ---- *)
Definition ps_pre (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (ot o s : Z) (buf cap failed : Z)
    (text bs : list Z) (live peak cnt fail : Z) : Prop :=
  fpreU tfibsegs B STK_put_string ly S U W regs mem md ch /\
  fs_heads B ly S U /\
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE /\
  YK11.getr regs 10%bv = w64 o /\ YK11.getr regs 11%bv = w64 s /\
  FSH_Fn_writer.wout_ok B tfibsegs ly S W mem o buf cap failed text /\
  fs_glob tfibsegs W mem live peak cnt fail /\
  (cap <> 0 -> In (buf - HEAD, HEAD) U) /\
  spZ regs <= o /\ o + 32 <= ot /\ ot mod 16 = 0 /\ ot <= ly_top ly /\
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp,
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\
     (ra < 4096 \/ nfp < alloc_ceiling)) /\
  (forall fp, fp = s0Z regs \/
     (exists r, In r ch /\ snd r = fp /\ bad_next (fst (fst r)) (ly_top ly) fp = false) ->
     fp <= o \/ o + 48 <= fp) /\
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) /\
  cstr_ok tfibsegs W mem s bs /\
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s (bs ++ [0]) /\
  WriterSpec.bytes_ok bs /\ WriterSpec.no_zero bs /\ plain_bytes bs /\
  (s + Z.of_nat (length bs) + 1 <= o \/ ot <= s) /\
  Z.of_nat (length text) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= FSH_Fn_writer.WMAX /\
  cap <= FSH_Fn_writer.WMAX /\ cap <= live /\
  FSH_Fn_writer.wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)).

(* ---- THE BUNDLE the walk carries at a put call's return. `ps` is the list of pieces already written, `ss` the
   symbolic state at the return (ps_ret_ss at the first two returns, ps_epi_ss at the third), `r` its pc. ---- *)
Definition ps_inv
    (* the entry, fixed *)
    (ly : alayout) (S : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (ot o s : Z) (bs : list Z)
    (buf cap failed : Z) (text : list Z) (live peak cnt fail : Z)
    (* the fake frame, granted once in the prologue *)
    (pos : Z) (lyc : alayout)
    (* the pieces written so far, and the state now *)
    (ps : list (list Z)) (r : Z) (ss : sstate)
    (ly' : alayout) (S' : astate) (U' : list (Z * Z)) (W' : world tfibsegs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (buf' : Z) : Prop :=
  let sp0 := spZ regs0 in
  let sp1 := 32 * ((sp0 - PS_FRAME_OWN) / 32) in
  let F := frame_addr lyc 0 pos in
  let FL := flag_addr lyc 0 pos in
  let X := fs_extraT ++ ps_xs regs0 FL ++ [Z_to_bv 64 (shadow_addr F)] in
  let st' := ps_st failed text cap cnt fail ps in
  (* the frame is live, and it is the only one this call added *)
  In (0, pos) (frames S') /\ frames S' = [(0, pos)] ++ frames S /\
  lyc = ly /\
  (* the walk's journal from the entry, at the raised window top, and the state's AR *)
  ajournal tfibsegs B (STK_put_string + (ot - sp0)) ot (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap)
    ly S W0 (unpoison U0 mem0) md0 [(0, pos)] ly' S' W' (unpoison U' mem') md'
    (FSH_Fn_writer.wevk cap st') /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  (* the symbolic state at the return, in ps_epilogue's env *)
  st_ok tfibsegs (Ereg regs' X) ss
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) /\
  ss_pc ss = r /\
  (* the registers the rest of the walk reads *)
  YK11.getr regs' 2%bv = Z_to_bv 64 sp1 /\ YK11.getr regs' 8%bv = Z_to_bv 64 sp0 /\
  YK11.getr regs' 9%bv = Z_to_bv 64 sp1 /\
  YK11.getr regs' 19%bv = Z_to_bv 64 o /\ YK11.getr regs' 21%bv = Z_to_bv 64 F /\
  YK11.getr regs' 22%bv = Z_to_bv 64 (shadow_addr F) /\
  YK11.getr regs' 23%bv = Z_to_bv 64 SHADOW_OFF /\ YK11.getr regs' 24%bv = Z_to_bv 64 F /\
  YK11.getr regs' 26%bv = Z_to_bv 64 s /\
  (* x3 and x4 only: x1 is NOT callee-saved (YG0d.acallee_saved is 2, 3, 4, 8, 9, 18..27), so a put leaves it
     unconstrained, and no consumer reads it - the epilogue returns through the SAVED ra at s0 - 8, not through
     x1 (a Theorem Labs lane's finding, 2026-10-29) *)
  YK11.getr regs' 3%bv = YK11.getr regs0 3%bv /\ YK11.getr regs' 4%bv = YK11.getr regs0 4%bv /\
  (* the frame's three chunk sets, on the memory now *)
  YP09.chunk_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem') sp1
    (YP09.mkChunk 80 (CVal 8 (SOff 24 0))) /\
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem') F) ps_hdr_chunks /\
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W') mem') (shadow_addr F)) ps_fsh_chunks /\
  (* the spec's relations, composed from the ENTRY to here *)
  FSH_Fn_writer.uswap U0 U' buf buf' cap /\
  FSH_Fn_writer.wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st')
    (WriterApp.w_text st') /\
  FSH_Fn_writer.wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st')
    (WriterApp.w_cnt st') /\
  FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
  wkeep tfibsegs W0 W' mem0 mem' sp0 ot o 32 /\
  cstr_ok tfibsegs W' mem' s bs /\
  (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
     fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
       (WriterApp.w_cnt st') (WriterApp.w_fail st')) /\
  (* what the NEXT put call needs of the string and the buffer *)
  FSH_Fn_writer.wsrc_kept B tfibsegs ly' S' U' W' mem' buf' s (bs ++ [0]) /\
  (WriterApp.w_cap st' <> 0 -> In (buf' - HEAD, HEAD) U') /\
  fs_heads B ly' S' U' /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') /\
  (forall a, sp1 <= a < ot -> apresent (w_H W') mem' a).

(* ---- THE CLOSING THEOREM, as the glue of four segments. ---- *)
Theorem ps_close :
  (* SEG 1: the entry, the fake-frame grant, the opening-quote put, its return *)
  (forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     (Q : world tfibsegs -> config -> Prop),
   ps_pre ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   (forall pos lyc ly' S' U' W' regs' mem' md' buf',
      ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
        [[34]] PS_OPEN_RET (ps_ret_ss PS_OPEN_RET (Z.of_nat (length bs)) psj_scs0 [ps_str_region (Z.of_nat (length bs))])
        ly' S' U' W' regs' mem' md' buf' ->
      SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 PS_OPEN_RET) mem' (seg_rom tfibsegs)) md') Q) ->
   SRr tfibsegs W (cfg_at tfibsegs A_put_string regs mem md) Q) ->
  (* SEG 2: the scan loop (or the empty arm), the run put, its return *)
  (forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     pos lyc ly1 S1 U1 W1 regs1 mem1 md1 buf1 (Q : world tfibsegs -> config -> Prop),
   ps_pre ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
     [[34]] PS_OPEN_RET (ps_ret_ss PS_OPEN_RET (Z.of_nat (length bs)) psj_scs0 [ps_str_region (Z.of_nat (length bs))])
     ly1 S1 U1 W1 regs1 mem1 md1 buf1 ->
   (forall ly2 S2 U2 W2 regs2 mem2 md2 buf2,
      ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
        (* psj_scs0, not psj_scs1: the seven slots at [sp1 + 8, sp1 + 64) are written only by the NON-EMPTY
           stretch to the loop head; the empty-string arm writes nothing (a Theorem Labs lane's finding). SEG3 loses nothing:
           psj_put2_put3 is generic in scs and psj_put3_close is stated at psj_scs0. *)
        [[34]; bs] PS_END_RET (ps_ret_ss PS_END_RET (Z.of_nat (length bs)) psj_scs0 [])
        ly2 S2 U2 W2 regs2 mem2 md2 buf2 ->
      SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 PS_END_RET) mem2 (seg_rom tfibsegs)) md2) Q) ->
   SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 PS_OPEN_RET) mem1 (seg_rom tfibsegs)) md1) Q) ->
  (* SEG 3: the closing-quote put and its return *)
  (forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     pos lyc ly2 S2 U2 W2 regs2 mem2 md2 buf2 (Q : world tfibsegs -> config -> Prop),
   ps_pre ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
     [[34]; bs] PS_END_RET (ps_ret_ss PS_END_RET (Z.of_nat (length bs)) psj_scs0 [])
     ly2 S2 U2 W2 regs2 mem2 md2 buf2 ->
   (forall ly3 S3 U3 W3 regs3 mem3 md3 buf3,
      ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
        [[34]; bs; [34]] PS_CLOSE_RET (ps_epi_ss PS_CLOSE_RET)
        ly3 S3 U3 W3 regs3 mem3 md3 buf3 ->
      SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 PS_CLOSE_RET) mem3 (seg_rom tfibsegs)) md3) Q) ->
   SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 PS_END_RET) mem2 (seg_rom tfibsegs)) md2) Q) ->
  (* SEG 4: the epilogue, from the third return to put_string_spec's post *)
  (forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     pos lyc ly3 S3 U3 W3 regs3 mem3 md3 buf3,
   ps_pre ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   ps_inv ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
     [[34]; bs; [34]] PS_CLOSE_RET (ps_epi_ss PS_CLOSE_RET)
     ly3 S3 U3 W3 regs3 mem3 md3 buf3 ->
   SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 PS_CLOSE_RET) mem3 (seg_rom tfibsegs)) md3)
     (fun W' c' => exists (st' : WriterApp.wst) buf' U',
        st' = WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs) /\
        FSH_Fn_writer.uswap U U' buf buf' cap /\
        FSH_Fn_writer.wpost B tfibsegs STK_put_string ot
          (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) regs ly S U W mem md
          (FSH_Fn_writer.wevk cap st') U'
          (fun ly' S' W'' regs' mem' md' =>
             FSH_Fn_writer.wout_ok B tfibsegs ly' S' W'' mem' o buf' (WriterApp.w_cap st')
               (WriterApp.w_failed st') (WriterApp.w_text st') /\
             FSH_Fn_writer.wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st')
               (WriterApp.w_cnt st') /\
             FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
             wkeep tfibsegs W W'' mem mem' (spZ regs) ot o 32 /\
             cstr_ok tfibsegs W'' mem' s bs /\
             (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
                fs_glob tfibsegs W'' mem' (live + WriterApp.w_cap st' - cap) peak'
                  (WriterApp.w_cnt st') (WriterApp.w_fail st')))
          W' c')) ->
  FSH_Fn_writer.put_string_spec B tfibsegs.
Proof.
intros SEG1 SEG2 SEG3 SEG4.
unfold FSH_Fn_writer.put_string_spec.
intros ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail
  HPRE Hheads Hfr G10 G11 HOUT HGLOB HHEAD Hspo Hoot Hot16 Hottop Hchain HFP HPRESENT Hcstr Hsrck
  Hbok Hnz Hplain Hsep Hwmax Hcap Hlive Hbp.
assert (PRE : ps_pre ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail).
{ unfold ps_pre.
  exact (conj HPRE (conj Hheads (conj Hfr (conj G10 (conj G11 (conj HOUT (conj HGLOB (conj HHEAD
    (conj Hspo (conj Hoot (conj Hot16 (conj Hottop (conj Hchain (conj HFP (conj HPRESENT (conj Hcstr
    (conj Hsrck (conj Hbok (conj Hnz (conj Hplain (conj Hsep (conj Hwmax (conj Hcap
    (conj Hlive Hbp)))))))))))))))))))))))). }
apply (SEG1 ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail _ PRE).
intros pos lyc ly1 S1 U1 W1 regs1 mem1 md1 buf1 INV1.
apply (SEG2 ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail
  pos lyc ly1 S1 U1 W1 regs1 mem1 md1 buf1 _ PRE INV1).
intros ly2 S2 U2 W2 regs2 mem2 md2 buf2 INV2.
apply (SEG3 ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail
  pos lyc ly2 S2 U2 W2 regs2 mem2 md2 buf2 _ PRE INV2).
intros ly3 S3 U3 W3 regs3 mem3 md3 buf3 INV3.
exact (SEG4 ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail
  pos lyc ly3 S3 U3 W3 regs3 mem3 md3 buf3 PRE INV3).
Qed.

End C.
