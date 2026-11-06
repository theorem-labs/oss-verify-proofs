(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178, for libreac/fuzz_identity's ASan build (lib/A). *)
(* reac_identity_ingest (fuzz_identity.asan 0x838fc, 0x538 bytes; listing offset AF_reac_identity_ingest = 0x31f0):
   its ASan-build contract treac_identity_ingest_spec.
   Form: cgif's caller-journal form (projects/cgif/cgif_file_fuzzer/proofs/lib/YC20.v tlzw_kept / tlzw_pR_ok / tlzw_post /
   tlzw_spec, CONVENTIONS.md §2), because the call writes up to 38 bytes of a record that lies in its caller's
   frame: LLVMFuzzerTestOneInput passes a6+352 (0x80c2c) and a6+112 (0x80cc8), where a6 is its class-4 side-stack
   frame (__asan_stack_malloc_4(768) at 0x80780) or, when there is no fake frame, the realigned machine stack
   (0x8079c..0x807b4). A callee whose apost_base FP covers a byte of its caller's frame cannot be composed by the
   caller (Reusable/YCbq.v:724-729 ajournal_sub and :1859-1860 accept only callee FP bytes that are in the
   caller's FP and in a block, or in a temporary block).
   The functional result is the released plain model, used as it is: lib/Prog/RcIdentModel.v (ING) and
   lib/Prog/reac_identity_ingest_c.v (ingest_refused, ingest_ret).
   This file holds the statement and the lemmas the walk shares; the walk is lib/A/Prog/IngestWalk.v (the main
   path, pb_reac_identity_ingest) and the arm segments stated in lib/A/Prog/IngestSeg.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ YC4b YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel RcIdentLib reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition A_reac_identity_ingest : Z := BASE + AF_reac_identity_ingest.
(* The stack the call needs, measured from the listing: the 32-byte frame (0x838fc addi sp,sp,-32; ra, s0, s1
   saved at sp+24, sp+16, sp+8), no realignment of sp, no side-stack frame, and no call on any path that
   returns (the only calls are the 23 __asan_report_* calls of the error path); plus ESTACK, CONVENTIONS §3. *)
Definition INGEST_STK : Z := 32 + ESTACK.
(* Allocator events and live heap bytes of one call: none. The plain model changes no byte outside the
   38-byte record (lib/Prog/reac_identity_ingest_c.v: munch [(id, id + 38)]) and the ASan listing calls
   neither the allocator nor the side-stack allocator. *)
Definition EV_INGEST : Z := 0.
Definition LIVE_INGEST : Z := 0.
Section h.
Variable B : asyms.
(* The caller's 38-byte identity record at id, as tlzw_pR_ok and tlzw_spec's pR premises state pR: it lies
   in one live side-stack frame of the caller's current state or in the machine stack, it does not meet the
   callee's stack window, the caller may write each byte and each byte is present, the shadow says each byte
   is addressable (the shadow checks of the ASan stores read it), and it holds idb. *)
Definition ting_rec_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (sp id : Z) (idb : list byte)
  : Prop :=
  id mod 8 = 0 /\
  ((exists cid pos, In (cid, pos) (frames Sc) /\
      forall a, id <= a < id + 38 -> in_zr a (frame_rng lyc (cid, pos))) \/
   (ly_stk_lo lyc <= id /\ id + 38 <= ly_stk_hi lyc)) /\
  (sp <= id \/ id + 38 <= sp - INGEST_STK) /\
  (forall a, id <= a < id + 38 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF id 38 /\
  length idb = RcIdentModel.ID_SIZE /\
  mbytes_at SEGS (mrestrict (w_H W) memc) id idb.
(* The payload p .. p + len: inside one live heap block of the caller's current state, and it holds pb. *)
Definition ting_pay_ok (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (p len : Z) (pb : list byte) : Prop :=
  (0 < len -> exists bi Li, In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + len <= bi + Li) /\
  mbytes_at SEGS (mrestrict (w_H W) memc) p pb.
(* What the call keeps is IdentCJ.v's shared shape `tcj_kept B INGEST_STK` (cgif lib/YC20.v:311-330
   tlzw_kept): everything but its own stack window and the bytes E it may write. The call allocates
   nothing and writes no heap byte. *)
(* The bytes the call may write: the record, and only when the call is not refused. On a refused call it
   writes nothing outside its own window, so the caller keeps every byte of its frames and blocks. *)
Definition ting_E (id p len : Z) : Z -> Prop :=
  fun a => reac_identity_ingest_c.ingest_refused id p len = false /\ id <= a < id + 38.
(* The post-condition: the caller's journal extended to the return state (same layout, allocator state and
   world: the call allocates nothing), callee-saved registers kept, a0 = the plain model's result, the bytes
   outside the record and the callee's window kept, and the record = the plain model's new record. *)
Definition treac_identity_ingest_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (id ad p len : Z) (idb pb : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 (k + EV_INGEST) /\
    aregs_preserved regs regs2 /\
    getr regs2 10 = w64 (reac_identity_ingest_c.ingest_ret id ad p len idb pb) /\
    tcj_kept B INGEST_STK lyc Sc W memc W mem2 (spZ regs) (ting_E id p len) /\
    (reac_identity_ingest_c.ingest_refused id p len = false ->
       mbytes_at SEGS (mrestrict (w_H W) mem2) id (snd (RcIdentModel.ING idb ad pb))).
Definition treac_identity_ingest_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (id ad p len : Z) (idb pb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 10 = w64 id -> getr regs 11 = w64 ad -> getr regs 12 = w64 p -> getr regs 13 = w64 len ->
  0 <= id < 2 ^ 64 -> 0 <= ad < 65536 -> 0 <= p < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  length pb = Z.to_nat len ->
  (reac_identity_ingest_c.ingest_refused id p len = false ->
     ting_rec_ok STK sp0 FP ly S own lyc Sc W memc (spZ regs) id idb /\
     ting_pay_ok lyc Sc W memc p len pb) ->
  st_nev Sc + EV_INGEST <= EV_MAX -> blocks_bytes Sc + LIVE_INGEST <= LIVE_MAX ->
  SRr SEGS W (cfg_at SEGS A_reac_identity_ingest regs memc mdc)
    (treac_identity_ingest_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id ad p len idb pb).
(* ---- the walk ------------------------------------------------------------------------------- *)
(* Section hypotheses (cgif lib/A/AChd.v:73-76, without its AMEMCMP): the allocator laws and the
   listing facts (the shadow GOT slot, object 1, and the shadow cell, object 30, that
   0x83914..0x8391c read). No runtime entry and no callee contract: no call is reached on a path
   that returns; the 23 calls of the listing are the __asan_report_* of the error path. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
(* The shadow base the call reads from the cell at 0x8391c, and the span the shadow checks live in. *)
Definition SB_ING : Z := 0x7fff8000.
Definition BXI : sv := SOff 32 0.
Definition Bspan_ING : Z * Z := (SB_ING, SB_ING + 2 ^ 44 - 1).
(* The state at the first slot: the 32-byte frame, the GOT slot (object 1) and the shadow cell
   (object 30) the prologue reads; atom 32 is the shadow base. *)
Definition ing_regions : smem := [ stack_region 32; got_regionP; bcell_regionP 32 ].
Definition ing_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB_ING SB_ING 0) ] [] [].
Definition ss_ing : sstate := mkSS AF_reac_identity_ingest sr_atoms ing_regions None ing_facts.
(* The extra atoms: 32 is the shadow base, 33 + j is payload byte j (j < 17, the most any arm reads). *)
Definition ing_extra (pb : list byte) : list word :=
  Z_to_bv 64 SB_ING ::
  map (fun j => Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j))) (seq 0 17).
Definition EI (regs : bvmap 5 word) (pb : list byte) : env := Eimg (Ereg regs (ing_extra pb)).
Lemma nth_map_seq_lt : forall (f : nat -> word) n j d, (j < n)%nat -> nth j (map f (seq 0 n)) d = f j.
Proof.
  intros f n j d Hj. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.
Lemma ing_extra_pay : forall pb j, (j < 17)%nat ->
  nth (S j) (ing_extra pb) (Z_to_bv 64 0) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j)).
Proof.
  intros pb j Hj. unfold ing_extra. cbn [nth].
  exact (nth_map_seq_lt (fun j => Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j))) 17 j _ Hj).
Qed.
Lemma ing_sp : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  2 ^ 46 + INGEST_STK <= spZ regs <= 2 ^ 47.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold INGEST_STK, ESTACK in *. lia.
Qed.
Lemma ing_sp_ceil : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  alloc_ceiling + INGEST_STK <= spZ regs.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.
(* An 8-byte value the symbolic state holds in a region chunk is in memory. *)
Lemma val8_of_st_ok_pi : forall E ss ms r n off e v,
  st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some n ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (ms_mem ms) (bv_unsigned (ew E n) + off) 8 v.
Proof.
  intros E ss ms r n off e v HS Hin Hb Hc He Hv.
  pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
  pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
  rewrite Hb in Hcs. cbn [base_val] in Hcs.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
  exact (val_of_chunk_ok SEGS E (ms_mem ms) _ off 8 e v Hck He Hv ltac:(lia)).
Qed.
(* What a run keeps when it changed memory only in the callee's frame [sp - 32, sp) and in E. *)
Lemma ing_kept_of : forall lyc Sc W memc mdc mem2 sp (E : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling + INGEST_STK <= sp -> sp <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> ~ E a ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, sp - INGEST_STK <= a < sp -> apresent (w_H W) mem2 a) ->
  (forall a, in_img SEGS a -> ~ E a) ->
  tcj_kept B INGEST_STK lyc Sc W memc W mem2 sp E.
Proof.
  intros lyc Sc W memc mdc mem2 sp E HAR Hsplo Hsphi KEEP HPRES HWIN HIMG.
  pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HS32 : INGEST_STK = 4128) by reflexivity.
  unfold tcj_kept. split.
  { intros a Ha Hw Hp. apply KEEP; [lia | lia | exact Hp]. }
  split.
  { intros b m i Hin Hi Hp.
    destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hce & _ & _).
    apply KEEP; [lia | lia | exact Hp]. }
  split.
  { intros a Hi Hns He. pose proof (Hsegs a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hrng.
    unfold kLowMemEnd in Hlow. apply KEEP; [lia | lia | exact (HIMG a Hi)]. }
  split.
  { intros cid pos a Hin Hr Hp.
    destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr) as (Hz & _).
    apply KEEP; [| lia | exact Hp].
    destruct Hr as [Hr | Hr]; unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr;
      pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _);
      pose proof (fs_frame_bytes_nonneg cid) as Hfb;
      [lia | pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb;
             unfold kLowMemEnd in *; lia]. }
  split; [intros a Ha Hw Hp; exact (HPRES a Hp)|].
  exact HWIN.
Qed.
Lemma ing_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) pb,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  st_ok_pi SEGS VAL (EI regs pb) ss_ing
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_identity_ingest) memc (seg_rom SEGS)))
  /\ sh_ok SEGS BXI [] (EI regs pb) (mrestrict (w_H W) memc).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pb HJ Hal16 Hlo Hhi.
  pose proof (ing_sp STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hlo Hhi) as Hsp.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 30 ltac:(lia)) as HcellR.
  pose proof (pal_got_cell B TL) as HgcD.
  split; [|constructor].
  rewrite restrict_mkst_fx. unfold ss_ing, A_reac_identity_ingest.
  set (E := EI regs pb) in *.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ing_extra pb)) n)
    by (intros n Hn; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_ING)
    by (rewrite EL by (unfold A_TEXT; lia); replace 32%nat with (32 + 0)%nat by lia; rewrite ew_Ereg_extra; reflexivity).
  assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
    by (apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
    by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ing_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold INGEST_STK, ESTACK in Hsp; lia|].
      split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold INGEST_STK, ESTACK in *. lia.
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
        [cbn [sv_denot]; rewrite Eo30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Eo30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 BXI SB_ING);
        [cbn [sv_denot BXI]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold SB_ING; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold ing_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) Eo30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold INGEST_STK, ESTACK in Hsp.
    revert Hsp HgotR HcellR HgcD. clear. intros. repeat split; lia.
  - split; [|split; exact I].
    cbn [ing_facts f_atoms atoms_ok].
    split.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
      unfold INGEST_STK, ESTACK in Hsp. split; [lia|]. split; [exact Hal16 | lia].
    + split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32.
      rewrite unsigned_lit_small by (unfold SB_ING; lia). rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
(* ---- the tail: 0x83cbc mv a0,a4; the three reloads; addi sp,sp,32; ret --------------------- *)
(* Every path of the function leaves through it with its result in a4. *)
Definition AF_ing_tail : Z := AF_reac_identity_ingest + 0x3c0.
Definition ing_tail_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) 0 32 0 0
      [ YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
        YP09.mkChunk 24 (CVal 8 (SOff 32 0)) ] ].
Definition ing_tail_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition ss_ing_tail : sstate := mkSS AF_ing_tail sr_atoms ing_tail_regions None ing_tail_facts.
(* The callee-saved registers the tail does not reload: sp, s0 and s1 are reloaded, the rest untouched. *)
Definition ING_KEPT : list (bv 5) := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ET (regsT regs : bvmap 5 word) : env :=
  Eimg (Ereg regsT [getr regs 1; getr regs 8; getr regs 9]).
Lemma in_kept_of : forall q, 0 <= q < 32 ->
  existsb (fun r : bv 5 => Z.eqb (bv_unsigned r) q) ING_KEPT = true -> In (Z_to_bv 5 q) ING_KEPT.
Proof.
  intros q Hq H. apply existsb_exists in H as (r & Hin & Hr). apply Z.eqb_eq in Hr.
  replace (Z_to_bv 5 q) with r; [exact Hin|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ing_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k
    (regs regsT : bvmap 5 word) (r : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
  YK0s.ret_ok (getr regs 1) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - INGEST_STK -> spZ regs <= sp0 ->
  getr regsT 2 = w64 (spZ regs - 32) ->
  getr regsT 14 = w64 r -> 0 <= r < 2 ^ 64 ->
  (forall q, acallee_saved q -> q <> 2 -> q <> 8 -> q <> 9 ->
     getr regsT (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_ing_tail) regsT memT mdT)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       aregs_preserved regs regs2 /\ getr regs2 10 = w64 r /\ (forall x, mem2 x = memT x)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regs regsT r
    HJ Hra Hal16 Hlo Hhi Hsp32 H14 Hr Hcs Mra Ms0 Ms1.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof (ing_sp STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regs HJ Hlo Hhi) as Hsp.
  unfold INGEST_STK, ESTACK in Hsp.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  remember (ET regsT regs) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsT [getr regs 1; getr regs 8; getr regs 9]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regsT 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsT _ 2 2%bv eq_refl)).
  assert (E14 : ew E 14 = getr regsT 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsT _ 14 14%bv eq_refl)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32)
    by (rewrite E2, Hsp32; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); replace 32%nat with (32 + 0)%nat by lia; rewrite ew_Ereg_extra; reflexivity).
  assert (E33 : ew E 33 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); replace 33%nat with (32 + 1)%nat by lia; rewrite ew_Ereg_extra; reflexivity).
  assert (E34 : ew E 34 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); replace 34%nat with (32 + 2)%nat by lia; rewrite ew_Ereg_extra; reflexivity).
  assert (UR : forall w : word, 0 <= bv_unsigned w < 2 ^ 64)
    by (intros w; pose proof (bv_unsigned_in_range 64 w) as Hw; change (bv_modulus 64) with (2 ^ 64) in Hw; exact Hw).
  assert (HAE : env_agree 32 (Ereg regsT [getr regs 1; getr regs 8; getr regs 9]) E)
    by (split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
  assert (HS : st_ok_pi SEGS VAL E ss_ing_tail
                 (restrict (w_H W) (mkst regsT (Z_to_bv 64 (BASE + AF_ing_tail)) memT (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_ing_tail. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold ing_tail_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (chunk_ok_val SEGS E _ (spZ regs - 32) 8 8 (SOff 34 0) (bv_unsigned (getr regs 9)));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | exact (UR (getr regs 9)) | zside |].
        replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact Ms1.
      + apply (chunk_ok_val SEGS E _ (spZ regs - 32) 16 8 (SOff 33 0) (bv_unsigned (getr regs 8)));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | exact (UR (getr regs 8)) | zside |].
        replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact Ms0.
      + apply (chunk_ok_val SEGS E _ (spZ regs - 32) 24 8 (SOff 32 0) (bv_unsigned (getr regs 1)));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | exact (UR (getr regs 1)) | zside |].
        replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact Mra.
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - split; [|split; exact I]. cbn [ing_tail_facts f_atoms atoms_ok].
      split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
      change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
      replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia.
      rewrite Z_mod_plus_full. exact Hal16. }
  assert (SHOK : sh_ok SEGS BXI [] E (mrestrict (w_H W) memT)) by constructor.
  unfold cfg_at. change (w64 (BASE + AF_ing_tail)) with (Z_to_bv 64 (BASE + AF_ing_tail)).
  assert (HM : forall x, memT x = memT x) by reflexivity.
  paj_run_tok RUN HS HJ SHOK Bspan_ING; [awr_ok_tac|].
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  split; [reflexivity|].
  exists (ms_regs ms), (ms_mem ms). eexists.
  split; [cbn [ms_regs]; rewrite R1, E32, Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split.
  { intros q Hq.
    destruct (Z.eq_dec q 2) as [->|Hq2].
    { replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R2. apply bv_eq. rewrite Usp, unsigned_lit_small by lia. unfold spZ. lia. }
    destruct (Z.eq_dec q 8) as [->|Hq8].
    { replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R8. exact E33. }
    destruct (Z.eq_dec q 9) as [->|Hq9].
    { replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R9. exact E34. }
    rewrite <- (Hcs q Hq Hq2 Hq8 Hq9).
    eapply (regs_kept_of_st_ok_pi _ _ _ _ _ ING_KEPT HS HAE ltac:(vm_compute; reflexivity)).
    apply in_kept_of; [unfold acallee_saved in Hq; lia|].
    assert (Hc : q = 3 \/ q = 4 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23
                 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
      by (unfold acallee_saved in Hq; lia).
    clear - Hc.
    repeat (destruct Hc as [Hc | Hc]; [try subst q; vm_compute; reflexivity |]).
    try subst q; vm_compute; reflexivity. }
  split.
  { rewrite R10. exact (eq_trans E14 H14). }
  intros x. apply HF. let rs := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
  let rs' := eval vm_compute in rs in change rs with rs' in HF |- *.
  intros (rr & [<- | []] & Hrr). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr. lia.
Qed.
(* Bytes a list of bytes holds are kept when memory is kept on them. *)
Lemma mbytes_kept : forall H (m m' : word -> option byte) a bs,
  (forall j, (j < length bs)%nat -> aview SEGS H m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  mbytes_at SEGS (mrestrict H m) a bs -> mbytes_at SEGS (mrestrict H m') a bs.
Proof.
  intros H m m' a bs Hk Hb j Hj. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j) (Hk j Hj)). exact (Hb j Hj).
Qed.
(* Where the record may lie, it is neither in the image nor in the callee's frame. *)
Lemma ting_rec_apart : forall STK sp0 FP ly S own lyc Sc W memc mdc sp id idb a,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling + INGEST_STK <= sp ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc sp id idb -> id <= a < id + 38 ->
  ~ in_img SEGS a /\ ~ (sp - INGEST_STK <= a < sp) /\ 4096 <= a /\ a < 2 ^ 47.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc mdc sp id idb a HAR Hceil Hslo Hshi HR Ha.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HR as (_ & HL & HD & _).
  assert (Hloc : (4096 <= a < alloc_ceiling /\ ~ in_img SEGS a) \/ (ly_stk_lo lyc <= a < ly_stk_hi lyc)).
  { destruct HL as [(cid & pos & Hin & Hr) | Hs].
    - left. pose proof (Hr a Ha) as Hra. unfold frame_rng, in_zr in Hra. cbn [fst snd] in Hra.
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H4096 & Hce & _).
      pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hin) as Himg.
      split; [lia|]. intros Hi. pose proof (pa_img_range a Hi). lia.
    - right. lia. }
  split; [intros Hi; destruct Hloc as [[_ Hn] | Hs]; [exact (Hn Hi) | pose proof (pa_img_range a Hi); lia]|].
  split; [lia|]. destruct Hloc as [[Hl _] | Hs]; lia.
Qed.
(* Where the record and a non-empty payload lie, as intervals. *)
Lemma ing_zones : forall STK sp0 FP ly S own lyc Sc W memc mdc sp id idb p len pb,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling + INGEST_STK <= sp ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc sp id idb ->
  ting_pay_ok lyc Sc W memc p len pb -> 0 < len ->
  (id + 38 <= IMG_LO \/ IMG_TOP <= id) /\ (p + len <= IMG_LO \/ IMG_TOP <= p) /\
  (p + len <= id \/ id + 38 <= p) /\ 4096 <= id /\ id + 38 <= 2 ^ 47 /\ 4096 <= p /\
  p + len <= alloc_ceiling /\ (sp <= id \/ id + 38 <= sp - INGEST_STK) /\
  exists bi Li, In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + len <= bi + Li.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc mdc sp id idb p len pb HAR Hceil Hslo Hshi HR HP Hlen.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HR as (_ & HL & HD & _). destruct HP as (HB & _).
  destruct (HB Hlen) as (bi & Li & Hin & Hb1 & Hb2).
  destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc bi Li HAR Hin) as (_ & H4096 & Hce & _).
  pose proof (blk_off_imgP B lyc Sc W memc mdc bi Li HAR Hin) as Himg.
  assert (HrqL : Li <= req_size Li) by (unfold req_size; destruct (Li =? 0) eqn:E; [apply Z.eqb_eq in E|]; lia).
  destruct HL as [(cid & pos & Hfin & Hr) | Hs].
  - pose proof (Hr id ltac:(lia)) as Hr0. pose proof (Hr (id + 37) ltac:(lia)) as Hr1.
    unfold frame_rng, in_zr in Hr0, Hr1. cbn [fst snd] in Hr0, Hr1.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (F4096 & Fce & _).
    pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hfin) as Fimg.
    pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc bi Li cid pos HAR Hin Hfin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    do 8 (split; [lia|]). exists bi, Li. split; [exact Hin | lia].
  - do 8 (split; [lia|]). exists bi, Li. split; [exact Hin | lia].
Qed.
(* The record region (atom 10 is id): no chunks, writable on [lo, hi). *)
Definition rec_region (lo hi : Z) : YP09.region := YP09.mkRegion (Some 10%nat) 0 38 lo hi [].
(* The payload region (atom 12 is p): its first n bytes, byte j as atom 33 + j. *)
Definition pay_chunk (j : nat) : YP09.chunk := YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j) 0)).
Definition pay_region (n : nat) : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 (Z.of_nat n) 0 0 (map pay_chunk (seq 0 n)).
Lemma rec_region_ok : forall E (m : word -> option byte) id lo hi,
  bv_unsigned (ew E 10) = id -> 0 <= id -> id + 38 <= 2 ^ 64 ->
  (forall o, lo <= o < hi -> writable_at SEGS m (id + o)) ->
  region_ok SEGS E m (rec_region lo hi).
Proof.
  intros E m id lo hi Hid H0 H1 Hw. unfold region_ok, rec_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hid.
  split; [lia|]. split; [lia|]. split; [exact Hw | constructor].
Qed.
Lemma pay_region_ok : forall E (m : word -> option byte) p (pb : list byte) n,
  (n <= 17)%nat -> (n <= length pb)%nat -> ew E 12 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> p + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < 17)%nat -> ew E (33 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j))) ->
  mbytes_at SEGS m p pb ->
  region_ok SEGS E m (pay_region n).
Proof.
  intros E m p pb n Hn17 Hnl E12 H0 H1 EP Hmb. unfold region_ok, pay_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E12, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  unfold pay_chunk.
  apply (chunk_ok_val SEGS E m p (Z.of_nat j) 1 (SOff (33 + j) 0) (RcIdentModel.bz (RcIdentModel.nthb pb j))).
  - cbn [sv_denot]. rewrite (EP j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb pb j)) as Hb.
    change (bv_modulus 8) with (2 ^ 8) in Hb. change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8). exact Hb.
  - lia.
  - intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
    rewrite (Hmb j ltac:(lia)). unfold RcIdentModel.nthb, RcIdentModel.bz.
    rewrite (nth_error_nth' pb (RcIdentModel.zb 0)) by lia. f_equal.
    pose proof (bv_unsigned_in_range 8 (nth j pb (RcIdentModel.zb 0))) as Hb.
    change (bv_modulus 8) with (2 ^ 8) in Hb.
    rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* A shadow entry from the range's addressability. *)
Lemma ing_shent : forall (W : world SEGS) (m : word -> option byte) E (n : nat) a len,
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len ->
  ew E 32 = Z_to_bv 64 SB_ING -> ew E n = Z_to_bv 64 a -> 4096 <= a -> a + len <= 2 ^ 47 -> 0 <= len ->
  (a + len <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= a) ->
  shent_ok SEGS BXI E (mrestrict (w_H W) m) (mkSHE n 0 len).
Proof.
  intros W m E n a len Hra E32 En Ha0 Ha1 Hl Happ.
  apply (shent_ok_of_range SEGS (w_H W) m E BXI n a len a 0 len Hra).
  - unfold BXI. rewrite (U_atom E 32 SB_ING E32) by (unfold SB_ING; lia). reflexivity.
  - exact (U_atom E n a En ltac:(lia)).
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
Qed.
(* The record is kept by a run that changed only the callee's frame. *)
Lemma ting_rec_kept : forall STK sp0 FP ly S own lyc Sc W memc mdc sp id idb mem2,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling + INGEST_STK <= sp ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  ting_rec_ok STK sp0 FP ly S own lyc Sc W memc sp id idb ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  mbytes_at SEGS (mrestrict (w_H W) mem2) id idb.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc mdc sp id idb mem2 HAR Hceil Hslo Hshi HR KEEP.
  pose proof HR as (_ & _ & _ & _ & _ & HL & HMB).
  apply (mbytes_kept _ memc mem2 id idb); [|exact HMB].
  intros j Hj. rewrite HL in Hj. unfold RcIdentModel.ID_SIZE in Hj.
  destruct (ting_rec_apart STK sp0 FP ly S own lyc Sc W memc mdc sp id idb (id + Z.of_nat j)
              HAR Hceil Hslo Hshi HR ltac:(lia)) as (_ & Hw & H4 & H47).
  apply KEEP; unfold INGEST_STK, ESTACK in Hw; lia.
Qed.
End h.
End f.
End d.
