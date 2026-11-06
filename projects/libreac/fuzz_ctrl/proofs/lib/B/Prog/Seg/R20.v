(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 647 of its 705 lines of code are new or changed and 953 lines of the source are left out. *)
(* Segment R20 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81a68, 0x81a9c], 14
   instructions, cut Inv_B81a68 -> cut Inv_B81aa0 (plan-asan-ubsan.md section 2, row R20; section 4, FREE =
   wrapper_free at 0x534b4). rule 24: no function proved (a slot segment).

   0x81a68 beqz a0 is taken (the bcmp wrapper returned 0, the entry cut), so the sink jump 0x81a6c is not reached.
   0x81a70 .. 0x81a84 sb s8 store the register s8 into the frame's own shadow bytes S(fr) + 322, 323, 316, 317,
   320, 321 (s3 = S(fr)), 0x81a88 j 81a98 skips 0x81a8c .. 0x81a94 (not reached), 0x81a98 mv a0,s4 (Phi_r) and
   0x81a9c jal wrapper_free, returning to 0x81aa0. The range has no instrumented shadow check and no arithmetic
   check branch to 0x82fa0.

   The free is the allocator's own contract AC.aa_free (a field of APIf), taken on the frame's law, never on its
   code, from the a_call_pre that fra_call_pre builds from FRA + ENT (ret_ok from the jal: ra = 0x81aa0;
   K = AK_FREE = 4096 <= FN_STACK), with afree_at's per-class premises for Bc = Tac_cls.Bc_of BE, BE the witness of
   ENT's 14th conjunct (Tac_cls.sl_free_cls): it removes the block (Phi_r, n_0) from the live list, so the exit cut
   carries the empty extra list. FRA / ENT move across the six shadow stores by RHelp.rh_sh_move (write set
   [S(fr) + 316, S(fr) + 324)), then across the free by Tac_slot.sl_mid / ent_call: a_call_post's frame clause
   keeps every byte the exit cut reads - the real stack at or above sp, the frame (the real stack or the side
   stack), the shadow bytes of real-stack, side-stack and image bytes, the musl client cells (the sink words),
   the image's RELRO bytes (frame_facts: the runtime owns none of them) and the input block - none of which the
   allocator owns (SlotInv.lw_not_owned, r20_client_byte, SlotInv.lw_client_img_shadow) or is in the free window
   [sp - 4096, sp), errno, the OOM flag or the freed block (the port of image A's r_free_cont,
   lib/A/Prog/Seg/R15.v). The read-only image bytes RBE reads (the box at BOXA and the row name) are kept by
   ro_agree on both sides. Turn 0 is not an identity or fragment turn, so RID / RFG at turn 1 are those of turn 0
   (r20_st1). Entry and exit are the official cuts Inv_B81a68_at / Inv_B81aa0_at of lib/B/Prog/SlotInv.v. RBE's
   conjuncts are kept across the free like its other spills and frame shadow bytes; s11 = 32 is kept by the run and
   the free (a callee-saved register).  v1.9.0 against the patched image: the pcs move +0x64, the stores use s8
   (patched s11), CUR's n - c is in s9 (patched s8), the 32 in s11 (patched s2), the frame is 3136 bytes, the
   musl client objects and sink words move +0x100, frame_RELRO is the one block [0x9f168, 0xa15e8). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcBox.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_cls RHelp RtmB.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.

(* A byte store `sb s11,k(s3)` into a cell run: le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion (the store
   hook of lib/B/Prog/Seg/R18.v). *)
Local Ltac fix_lit_store ::=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) => change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

(* ---- image placement, on the image's segment table (prover a Theorem Labs lane's lib/B/Prog/Seg/R7.v copies) ---- *)

Definition r20_img_cov (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma r20_img_cov_in : forall lo hi x, r20_img_cov lo hi = true -> lo <= x < hi -> AC.a_in_img x.
Proof.
  intros lo hi x H Hx. unfold r20_img_cov in H. apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (H1 & H2). apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin | lia].
Qed.

Lemma r20_ag_cov : forallb (fun p => r20_img_cov (fst p) (fst p + snd p)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r20_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r20_ag_cov (lo, len) Hin) as H. cbn [fst snd] in H.
  exact (r20_img_cov_in _ _ _ H Hr).
Qed.

Lemma r20_sink_cov_a : r20_img_cov 0x5fc8e1 0x5fc8e2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r20_sink_cov_b : r20_img_cov 0x5fcd40 0x5fcd50 = true.
Proof. vm_compute. reflexivity. Qed.
(* The rodata block that holds the box at BOXA and the catalogue rows' names. *)
Lemma r20_rod_cov : r20_img_cov 0x21000 0x22000 = true.
Proof. vm_compute. reflexivity. Qed.

(* The client objects of musl's stdio the sink words live in (Contract.v a_client). *)
Lemma r20_client_a : forall a, 0x5dc680 <= a < 0x5dc680 + 131728 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5dc680, 131728. split; [cbn; tauto | exact Ha]. Qed.
Lemma r20_client_b : forall a, 0x5fc918 <= a < 0x5fc918 + 4320 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5fc918, 4320. split; [cbn; tauto | exact Ha]. Qed.

(* The image's RELRO globals lie in [0x9f168, 0xa15e8). *)
Lemma r20_relro_range : forall a, in_globals AF.frame_RELRO a -> 0x9f168 <= a < 0xa15e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AF.frame_RELRO in Hin. cbn [In] in Hin.
  destruct Hin as [E|[]]; inversion E; subst; lia.
Qed.

(* Every byte of [0x21000, 0x22000) is read-only image (checked by computation). *)
Definition r20_ro_run (a : Z) (n : nat) : bool := forallb (fun k => ro_addr rsegs (wa (a + Z.of_nat k))) (seq 0 n).

Lemma r20_ro_run_ok : forall a n, r20_ro_run a n = true -> forall x, a <= x < a + Z.of_nat n ->
  ro_addr rsegs (wa x) = true.
Proof.
  intros a n H x Hx. unfold r20_ro_run in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - a)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  replace (a + (x - a)) with x in H by lia. exact H.
Qed.

Lemma r20_rod_ro : r20_ro_run 0x21000 4096 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- memory transfers ---- *)

(* bytes_at survives a memory change that keeps each byte of its range. *)
Lemma r20_bkeep : forall (mem mem' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs.
Proof.
  intros mem mem' a bs H (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). rewrite <- !rh_mbyte_mrd. apply H. lia.
Qed.

(* addressable survives a memory change that keeps the shadow byte of each byte of the range. *)
Lemma r20_addr_keep : forall (m m' : word -> option byte) p n,
  addressable m p n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. rewrite <- rh_mbyte_mrd in Hb |- *. rewrite (HK i Hi).
  exact Hb.
Qed.

(* Read-only bytes agree with the image on both sides of a run that keeps ro_agree. *)
Lemma r20_ro_bytes : forall (m m' : word -> option byte) a bs,
  MemNorm.ro_agree rsegs m -> MemNorm.ro_agree rsegs m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ro_addr rsegs (wa x) = true) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs R R' Hro H. apply (r20_bkeep m m' a bs); [|exact H].
  intros x Hx. rewrite !rh_mbyte_mrd. rewrite (R' _ (Hro x Hx)), (R _ (Hro x Hx)). reflexivity.
Qed.

(* A callee-saved register of an allocator entry, at a register named by a numeral. *)
Lemma r20_regs_kept_at : forall regs regs' (r : reg) (z : Z),
  AC.a_regs_kept regs regs' -> AC.a_callee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HK Hc <-. exact (HK z Hc). Qed.

(* Turn 0 is neither an identity turn (3, 4) nor a fragment turn (5, 6): the records of turn 1 are those of
   turn 0. *)
Lemma r20_st1 : forall inp, rt_st inp 1 = rt_st inp 0.
Proof.
  intros inp. cbn [rt_st]. change (Z.of_nat 0) with 0.
  destruct (rt_n inp 0 =? 0); reflexivity.
Qed.

(* The catalogue rows' names (when a row names one) are rodata bytes of [0x21000, 0x22000) (computed over the 11
   rows). *)
Definition r20_name_ok (row : list byte) : bool :=
  (RcSynth.has row =? 0) || (RcSynth.rname row =? 0) ||
  ((0x21000 <=? RcSynth.rname row) &&
   (RcSynth.rname row + Z.of_nat (length (img_cstr (RcSynth.rname row) 16)) <=? 0x22000)).

Lemma r20_name_ok_rows : forall inp, r20_name_ok (rt_mb inp) = true.
Proof.
  intros inp. unfold rt_mb. pose proof (rb_istar_range inp) as H.
  remember (istar inp) as k eqn:Ek. clear Ek.
  assert (Hk : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10)
    by lia.
  destruct Hk as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma r20_name_rng : forall inp, RcSynth.has (rt_mb inp) <> 0 /\ RcSynth.rname (rt_mb inp) <> 0 ->
  forall i, 0 <= i < Z.of_nat (length (rt_nb inp)) -> 0x21000 <= RcSynth.rname (rt_mb inp) + i < 0x22000.
Proof.
  intros inp (H1 & H2) i Hi. pose proof (r20_name_ok_rows inp) as H. unfold r20_name_ok in H.
  apply Z.eqb_neq in H1, H2. rewrite H1, H2 in H. cbn [orb] in H.
  apply andb_true_iff in H as (Ha & Hb). apply Z.leb_le in Ha, Hb. unfold rt_nb in Hi. lia.
Qed.

(* ---- the Lib-level run of [0x81a68, 0x534b4) ---- *)

Lemma r20_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    a0v = Z_to_bv 64 0 ->
    rw_cells rsegs m (bv_unsigned s3v + 316) [CB 8 junk] ->
    stk rsegs m (bv_unsigned s3v + 316) (bv_unsigned s3v + 324) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x534b4) fc None m' (seg_rom rsegs) /\
         getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = s4 /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
         getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 316, bv_unsigned s3v + 324)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v + 316) (bv_unsigned s3v + 324))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81a68) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m junk -> RWsh ST.
  pose proof (rw_cells_bound _ _ _ _ RWsh) as HBsh. cbn [cells_size csize Nat.add] in HBsh.
  pose proof (munch_refl [(bv_unsigned s3v + 316, bv_unsigned s3v + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 81a68 beqz a0 (taken) *)
  step. if_true.
  (* 81a70 .. 81a84 : the six shadow stores *)
  step. step. step. step. step. step.
  (* 81a88 j 81a98 ; 81a98 mv a0,s4 ; 81a9c jal wrapper_free *)
  step. step. step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 17 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The one place this file takes a_laws_client apart (a Theorem Labs lane 15:32Z): the runtime owns no client byte. *)
Lemma r20_client_byte : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.in_blocks AC.a_client a ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a.
Proof.
  intros H mem md a HAH Hcl.
  decompose [and] (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH).
  match goal with Hx : AC.in_blocks AC.a_client a -> ~ _ |- _ => exact (Hx Hcl) end.
Qed.

Lemma seg_R20 : forall b : nat,
  Hat B APIf ra (Inv_B81aa0_at B APIf ra) b -> Hat B APIf ra (Inv_B81a68_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hb6 & HHB & H22 & HOUR & HCUR & HRBE & H21 & Hb0 & HRF & Ha0 & H27)).
  subst c. subst b. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (rh_sh_in B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as Hshin.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (W0 & W1 & _); split; [exact W0 | exact W1]).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HA4 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  unfold AC.GT in HGTfr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfrhi : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (Hshin (Sfr fr + 391) ltac:(lia)) as (IS & _).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HSfrGT : AC.GT <= Sfr fr) by (unfold Sfr, shadow_addr, ASAN_K, AC.GT; Z.div_mod_to_equations; lia).
  assert (Hs3 : bv_unsigned (getr regs 19) = Sfr fr).
  { unfold rg in Hr19. rewrite Hr19. apply MState.unsigned_lit. unfold AC.GT, HIGHMEM_BEG in *. lia. }
  (* the turn's records and the harness block *)
  pose proof HRF as (HRB0 & Hnz & H20 & HF).
  destruct (rb_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0) in Hnb, HLF.
  (* the eight shadow bytes S(fr) + 316 .. + 323: a cell run, present and writable *)
  assert (HSTsh : stk rsegs mem (Sfr fr + 316) (Sfr fr + 324)).
  { pose proof HRT as (_ & HSW0 & _).
    split; [unfold AC.GT in HSfrGT; lia|]. split; [unfold HIGHMEM_BEG in HSfrhi; lia|].
    intros a Ha. destruct (Hshin a ltac:(lia)) as (Hsa & _). exact (HSW0 a Hsa). }
  assert (HRWsh : exists junk, rw_cells rsegs mem (Sfr fr + 316) [CB 8 junk]).
  { pose proof HRT as (_ & HSW0 & _).
    destruct (rh_bytes_of_present 8%nat mem (Sfr fr + 316) ltac:(unfold AC.GT in HSfrGT; lia)
                ltac:(unfold HIGHMEM_BEG in HSfrhi; lia)) as (junk & Hj & Hjl).
    { intros k Hk. destruct (Hshin (Sfr fr + 316 + Z.of_nat k) ltac:(lia)) as (Hsa & _).
      exact (proj2 (HSW0 _ Hsa)). }
    exists junk. rewrite <- Hjl. apply rh_rwc_CB; [exact Hj|]. rewrite Hjl.
    split; [unfold AC.GT in HSfrGT; lia|]. split; [unfold HIGHMEM_BEG in HSfrhi; cbn; lia|].
    intros i Hi. cbn in Hi. destruct (Hshin (Sfr fr + 316 + i) ltac:(lia)) as (Hsa & _).
    exact (proj1 (HSW0 _ Hsa)). }
  destruct HRWsh as (junk & HRWsh).
  (* the run to the allocator's entry *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81a68) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x534b4 /\
       getr R 1 = Z_to_bv 64 0x81aa0 /\ getr R 10 = getr regs 20 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27 /\ getr R 18 = getr regs 18 /\
       munch [(Sfr fr + 316, Sfr fr + 324)] mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (Sfr fr + 316) (Sfr fr + 324))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg, a0v in Ha0.
    eapply evt_mono.
    - apply (r20_evt) with (junk := junk);
      repeat match goal with
      | |- context [bv_unsigned ?s] =>
          change (bv_unsigned s) with (bv_unsigned (getr regs 19)); rewrite Hs3
      end;
      [ exact Ha0 | exact HRWsh | exact HSTsh ].
    - intros ms' (R & m' & E & P1 & P10 & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 &
                  P25 & P26 & P27 & MU & WM & ST).
      exists R, (Z_to_bv 64 0x534b4), m'. split; [exact E|].
      split; [reflexivity|].
      split; [exact P1|]. split; [exact P10|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P20|]. split; [exact P21|].
      split; [exact P22|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|].
      split; [exact P26|]. split; [exact P27|]. split; [exact P18|].
      match type of MU with
      | context [bv_unsigned ?s] => change (bv_unsigned s) with (bv_unsigned (getr regs 19)) in MU, ST
      end.
      rewrite Hs3 in MU, ST.
      split; [exact MU|]. split; [exact WM | exact ST]. }
  intros R pc' mem1 regs1 md1
    (Hpc & K1 & K10 & K2 & K3 & K4 & K8 & K9 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K18 &
     MU1 & WM1 & ST1) Hreg Hmat.
  subst pc'.
  assert (E1 : getr regs1 1 = Z_to_bv 64 0x81aa0) by (rewrite Hreg; exact K1).
  assert (E10 : getr regs1 10 = Z_to_bv 64 phi) by (rewrite Hreg, K10; unfold rg in H20; exact H20).
  assert (E2 : getr regs1 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs1 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs1 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs1 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs1 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs1 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs1 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs1 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E23 : getr regs1 23 = getr regs 23) by (rewrite Hreg; exact K23).
  assert (E24 : getr regs1 24 = getr regs 24) by (rewrite Hreg; exact K24).
  assert (E25 : getr regs1 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs1 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E27 : getr regs1 27 = getr regs 27) by (rewrite Hreg; exact K27).
  (* step 1: the six shadow stores *)
  destruct (rh_sh_move B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs1 mem mem1 md 316 324 HFRA HENT
              ltac:(lia) ltac:(lia) ltac:(lia) MU1 WM1
              ltac:(intros qq Hqq; destruct ST1 as (_ & _ & HST1); exact (proj2 (HST1 qq Hqq)))
              E2 E3 E4 E8 E9 E19 E26) as (HFRAs & HENTs).
  assert (HFRA1 : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs1 mem1 md1)
    by exact (sl_fra_move B APIf ra g fr _ regs1 regs1 mem1 md md1 HFRAs
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
  assert (HENT1 : ENT APIf g (hb1 phi (rnb g 0)) mem1 md1) by exact (ent_mat APIf g _ mem1 md md1 HENTs Hmat).
  set (W1 := [(Sfr fr + 316, Sfr fr + 324)]).
  assert (HoutW1 : forall x, (x < Sfr fr + 316 \/ Sfr fr + 324 <= x) -> outside W1 x)
    by (intros x Hx; unfold W1; cbn [outside]; split; [lia | exact I]).
  assert (HappW1 : forall x, app_mem x -> outside W1 x).
  { intros x Hx. destruct (rh_out_dec W1 x) as [Ho|Ho]; [exact Ho|]. exfalso.
    unfold W1 in Ho. cbn [outside] in Ho. destruct (Hshin x ltac:(lia)) as (Hsx & _).
    exact (app_not_shadow x Hx Hsx). }
  assert (HRBE1 : RBE g fr regs1 mem1).
  { apply (rh_RBE_keep_sh g fr regs regs1 W1 mem mem1 A HRBE MU1 Hfr8 ltac:(unfold AC.GT; lia) Hr9 ltac:(lia)
             HA4 E9).
    - intros x Hx. apply HoutW1. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    - intros x Hx. unfold W1 in Hx. cbn [outside] in Hx. lia. }
  assert (HRB1 : RB g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) regs1 mem1).
  { apply (rh_RB_keep g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) regs regs1 W1 mem mem1 MU1
             (rb_RID_len (g_in g) 0) (rb_RFG_len (g_in g) 0 ltac:(lia)));
      [ intros x Hx; apply HappW1, Happfr; lia | exact E22 | exact E23 | exact E25 | exact HRB0 ]. }
  (* ---- the free ---- *)
  pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & HRimg & HOWNG & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi (rnb g 0)) regs1 mem1 md1 HFRA1) as Hapart.
  pose proof (fra_in_apart B APIf ra g fr (hb1 phi (rnb g 0)) regs1 mem1 md1 HFRA1) as Hinap.
  pose proof HFRA1 as HF1.
  destruct HF1 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr2_1 & Hspm1 & Haspz1 &
    Hstklo1 & Hr4_1 & Hr8_1 & Hr9_1 & Hr3_1 & Hr19_1 & Hr26_1 & Hfrm1 & Hs5_1 & HAm1 & HAS1 & Hspa1 & Hfa1 &
    HA448_1 & HS4_1 & HAPP1 & Hspill1 & Hsel1 & Hfr56_1 & Hloc1 & Hhdr1_1 & Hhdr2_1 & Hsh1 & Hwin1 & Hsaved1 &
    Herrno1 & HAG1 & HWA1 & HSHI1_1 & HSHI2_1 & HSHI3_1 & Hhb1 & Hlive1 & Hinb1 & Hinblk1).
  assert (Hasp1 : AC.aspZ regs1 = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
  rewrite Hasp1 in Haspz1. subst sp1.
  assert (EA1 : A1 = A)
    by (exact (rh_rg9_eq regs A A1 Hr9 ltac:(unfold rg in *; rewrite <- E9; exact Hr9_1) HA64
                 ltac:(unfold APPMEM_END in *; lia))).
  subst A1.
  assert (HERRv : AC.a_errno AC.ASYMS = 6145452) by reflexivity.
  assert (HOOMv : AC.as_oom AC.ASYMS = 1227040) by reflexivity.
  assert (HKF : AC.AK_FREE = 4096) by reflexivity.
  rewrite Hasp1 in Hapart.
  assert (Hstkhi : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem1 md1 HAH1).
  assert (HBLK : In (phi, rnb g 0) (hb1 phi (rnb g 0) ++ g_H g)) by (left; reflexivity).
  pose proof (lw_blocks (APIf rc) (hb1 phi (rnb g 0) ++ g_H g) mem1 md1 phi (rnb g 0) HAH1 HBLK) as HLB.
  pose proof (lwb_low _ _ _ _ _ _ HLB) as Hp4096. pose proof (lwb_end _ _ _ _ _ _ HLB) as Hblkle.
  pose proof (lwb_byte _ _ _ _ _ _ HLB) as Hbyte. pose proof (lwb_byte_not_fs (APIf rc) _ _ _ _ _ HLB) as Hbnfs.
  (* a side-stack byte lies above the image and below stklo *)
  assert (FSC : forall a, 0 <= a < 2 ^ 64 -> AC.a_in_fs AC.ASYMS mem1 a ->
             AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1 /\ app_mem a).
  { intros a Ha (bb & Hbb & Hwm & Hb1 & Hb2).
    destruct (lw_fs_place (APIf rc) _ mem1 md1 bb HAH1 Hwm Hbb) as [Hg Hfsk _ Hfsa].
    split; [lia|]. apply Hfsa. lia. }
  (* where a frame byte lies *)
  assert (FRAME : forall a, fr <= a < fr + 3136 ->
             (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1 <= a < APPMEM_END \/
              (AC.a_in_fs AC.ASYMS mem1 a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1)) /\
             app_mem a).
  { intros a Ha. destruct Hloc1 as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha) as Hr. split; [left; exact Hr|]. unfold app_mem. right. lia.
    - destruct (FSC a ltac:(unfold APPMEM_END in *; lia) (Hfs a Ha)) as (Ha1 & Ha2).
      split; [right; split; [exact (Hfs a Ha) | exact Ha1] | exact Ha2]. }
  (* the frame, image bytes and shadow bytes are apart from the freed block *)
  assert (BLKFR : forall a, fr <= a < fr + 3136 -> ~ (phi <= a < phi + rnb g 0)).
  { intros a Ha Hb. destruct (FRAME a Ha) as ([Hs|[Hfs _]] & _).
    - lia.
    - exact (Hbnfs a Hb Hfs). }
  assert (NBLK : forall a, AC.a_in_img a -> ~ (phi <= a < phi + rnb g 0)).
  { intros a Himg Hb. destruct (Hbyte a Hb) as (_ & _ & Hni & _). exact (Hni Himg). }
  assert (NBLKsh : forall a, in_shadow a -> ~ (phi <= a < phi + rnb g 0)).
  { intros a Hshd Hb. destruct (Hbyte a Hb) as (Happ & _). exact (app_not_shadow a Happ Hshd). }
  (* the call pre *)
  assert (Hpre1 : AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                    AC.AK_FREE (hb1 phi (rnb g 0) ++ g_H g) regs1 mem1 md1).
  { apply (fra_call_pre B APIf ra g fr (hb1 phi (rnb g 0)) regs1 mem1 md1 AC.AK_FREE HFRA1 HENT1).
    - unfold YK0s.ret_ok. rewrite E1. vm_compute. reflexivity.
    - rewrite HKF, HFN. lia. }
  pose proof (AC.aa_free AC.ASYMS AsanRTInv.RT (APIf rc)) as HFREE.
  unfold AC.afree_contract, AC.afree_at in HFREE.
  assert (EFREE : AC.as_free AC.ASYMS = 0x534b4) by reflexivity.
  rewrite EFREE in HFREE.
  (* the free's per-class premises: ENT's own class witness BE, with Bc = Bc_of BE over the call heap
     (phi, n_0) :: g_H g (Tac_cls.sl_free_cls) *)
  destruct (sl_free_cls APIf g (hb1 phi (rnb g 0)) mem1 md1 phi (rnb g 0) HENT1) as (BE & _ & _ & HBc & HBroom).
  eapply (SR_bind rsegs).
  { exact (HFREE [] (g_H g) regs1 mem1 md1 phi (rnb g 0) (Bc_of BE) Hpre1 E10 HBc HBroom). }
  intros c' (regs' & mem' & md'' & Ec' & Hcp & Herrk).
  rewrite E1 in Ec'. subst c'.
  pose proof Hcp as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof Hcp as Hkept; apply AC.a_call_post_regs in Hkept.
  pose proof Hcp as Hsk'; apply AC.a_call_post_stklo in Hsk'.
  pose proof Hcp as Hro'; apply AC.a_call_post_ro in Hro'.
  pose proof Hcp as Hmod; apply AC.a_call_post_model in Hmod.
  pose proof (AC.a_call_post_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hfk.
  pose proof (AC.a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinw.
  pose proof (AC.a_call_post_win_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinp.
  assert (Htp16 : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem1 (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (F2 : getr regs' 2 = getr regs1 2)
    by (apply (r20_regs_kept_at regs1 regs' 2 2 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F3 : getr regs' 3 = getr regs1 3)
    by (apply (r20_regs_kept_at regs1 regs' 3 3 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F4 : getr regs' 4 = getr regs1 4)
    by (apply (r20_regs_kept_at regs1 regs' 4 4 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F8 : getr regs' 8 = getr regs1 8)
    by (apply (r20_regs_kept_at regs1 regs' 8 8 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F9 : getr regs' 9 = getr regs1 9)
    by (apply (r20_regs_kept_at regs1 regs' 9 9 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F19 : getr regs' 19 = getr regs1 19)
    by (apply (r20_regs_kept_at regs1 regs' 19 19 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F21 : getr regs' 21 = getr regs1 21)
    by (apply (r20_regs_kept_at regs1 regs' 21 21 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F22 : getr regs' 22 = getr regs1 22)
    by (apply (r20_regs_kept_at regs1 regs' 22 22 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F23 : getr regs' 23 = getr regs1 23)
    by (apply (r20_regs_kept_at regs1 regs' 23 23 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F24 : getr regs' 24 = getr regs1 24)
    by (apply (r20_regs_kept_at regs1 regs' 24 24 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F25 : getr regs' 25 = getr regs1 25)
    by (apply (r20_regs_kept_at regs1 regs' 25 25 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F26 : getr regs' 26 = getr regs1 26)
    by (apply (r20_regs_kept_at regs1 regs' 26 26 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (F27 : getr regs' 27 = getr regs1 27)
    by (apply (r20_regs_kept_at regs1 regs' 27 27 Hkept ltac:(unfold AC.a_callee_saved; lia)); apply bv_eq; reflexivity).
  assert (FSPOST : forall a, AC.a_in_fs AC.ASYMS mem1 a -> AC.a_in_fs AC.ASYMS mem' a).
  { intros a (bb & Hbb & Hwm & Hb). exists bb. split; [exact Hbb|]. split; [|exact Hb].
    intros k Hk. rewrite (Htp16 (Z.of_nat k) ltac:(lia)). exact (Hwm k Hk). }
  (* a byte not owned (before / after), off the free window, errno, the flag and the freed block, is kept *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g 0) ++ g_H g) mem1 md1 a ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md'' a ->
      ~ (sp - 4096 <= a < sp) -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
      a <> AC.as_oom AC.ASYMS -> ~ (phi <= a < phi + rnb g 0) ->
      mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)).
  { intros a Ha Ho1 Ho2 Hw He Hoo Hnt. apply (Hfk a Ha Ho1 Ho2); [| exact He | exact Hoo | exact Hnt].
    unfold AC.a_window. rewrite HKF, Hasp1. exact Hw. }
  (* a real-stack or side-stack byte and its shadow byte are not the allocator's, before or after *)
  assert (LOC : forall a,
      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1 <= a < APPMEM_END \/
       (AC.a_in_fs AC.ASYMS mem1 a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1)) ->
      0 <= a < 2 ^ 64 /\ AC.GT <= a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g 0) ++ g_H g) mem1 md1 a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (rnb g 0) ++ g_H g) mem1 md1 (shadow_addr a) /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md'' a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md'' (shadow_addr a)).
  { intros a Hl.
    assert (Hpl : AC.in_blocks (hb1 phi (rnb g 0) ++ g_H g) a \/ AC.in_slack (hb1 phi (rnb g 0) ++ g_H g) a \/
                  AC.a_in_fs AC.ASYMS mem1 a \/ AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1 <= a < APPMEM_END)
      by (destruct Hl as [Hs|[Hfs _]]; [right; right; right; exact Hs | right; right; left; exact Hfs]).
    assert (Hql : AC.in_blocks ([] ++ g_H g) a \/ AC.in_slack ([] ++ g_H g) a \/ AC.a_in_fs AC.ASYMS mem' a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md'' <= a < APPMEM_END).
    { rewrite Hsk'. destruct Hl as [Hs|[Hfs _]];
        [right; right; right; exact Hs | right; right; left; exact (FSPOST a Hfs)]. }
    destruct (lw_not_owned (APIf rc) _ mem1 md1 a HAH1 Hpl) as [N1 N2].
    destruct (lw_not_owned (APIf rc) _ mem' md'' a HAH' Hql) as [N3 N4].
    split; [destruct Hl as [Hs|[_ Hs]]; unfold AC.GT, HIGHMEM_BEG, APPMEM_END in *; lia|].
    split; [destruct Hl as [Hs|[_ Hs]]; unfold AC.GT, HIGHMEM_BEG in *; lia|].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3 | exact N4]. }
  assert (KLOC : forall a,
      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1 <= a < APPMEM_END \/
       (AC.a_in_fs AC.ASYMS mem1 a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1)) ->
      ~ (sp - 4096 <= a < sp) -> ~ (phi <= a < phi + rnb g 0) ->
      mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)).
  { intros a Hl Hw Hnt. destruct (LOC a Hl) as (Hr & Hg & N1 & _ & N3 & _).
    apply KEEP; [exact Hr | exact N1 | exact N3 | exact Hw | unfold AC.GT in Hg; lia | unfold AC.GT in Hg; lia
                | exact Hnt]. }
  assert (KST : forall a, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1 <= a < APPMEM_END ->
      ~ (sp - 4096 <= a < sp) ->
      mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)).
  { intros a Hs Hw. apply KLOC; [left; exact Hs | exact Hw | lia]. }
  assert (KSH : forall a,
      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1 <= a < APPMEM_END \/
       (AC.a_in_fs AC.ASYMS mem1 a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem1 md1)) ->
      app_mem a -> mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem1 (shadow_addr a)).
  { intros a Hl Hap. destruct (LOC a Hl) as (_ & _ & _ & N2 & _ & N4).
    pose proof (shadow_of_app a Hap) as Hsh_a. pose proof (in_shadow_range _ Hsh_a) as Hsr.
    pose proof (NBLKsh (shadow_addr a) Hsh_a) as Hnbs.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh_a.
    refine (proj1 (KEEP _ _ N2 N4 _ _ _ Hnbs)); unfold HIGHMEM_BEG in *; lia. }
  assert (KFR : forall a, fr <= a < fr + 3136 -> mbyte rsegs mem' a = mbyte rsegs mem1 a).
  { intros a Ha. destruct (FRAME a Ha) as (Hl & _). exact (proj1 (KLOC a Hl (Hapart a Ha) (BLKFR a Ha))). }
  assert (KFRsh : forall a, fr <= a < fr + 3136 ->
            mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem1 (shadow_addr a)).
  { intros a Ha. destruct (FRAME a Ha) as (Hl & Hap). exact (KSH a Hl Hap). }
  (* the musl client cells and the shadow bytes of image bytes *)
  assert (KCL : forall x, 0x5dc680 <= x < 0x5fd9f8 -> AC.in_blocks AC.a_client x -> AC.a_in_img x ->
            mbyte rsegs mem' x = mbyte rsegs mem1 x).
  { intros x Hxr Hcl Himg. pose proof (img_below_GT x Himg) as Hr. unfold AC.GT in Hr.
    refine (proj1 (KEEP x _ _ _ _ _ _ (NBLK x Himg))).
    - lia.
    - exact (r20_client_byte _ mem1 md1 x HAH1 Hcl).
    - exact (r20_client_byte _ mem' md'' x HAH' Hcl).
    - unfold HIGHMEM_BEG in *; lia.
    - rewrite HERRv; lia.
    - rewrite HOOMv; lia. }
  assert (KIMGsh : forall x, AC.a_in_img x -> mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem1 (shadow_addr x)).
  { intros x Himg. pose proof (img_below_GT x Himg) as Hr. unfold AC.GT in Hr.
    assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; unfold app_mem, LOWMEM_END; left; lia).
    pose proof (in_shadow_range _ Hshd) as Hrr.
    pose proof Hshd as Hshd'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
    refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ (NBLKsh _ Hshd))).
    - lia.
    - exact (lw_client_img_shadow (APIf rc) _ mem1 md1 x HAH1 Himg).
    - exact (lw_client_img_shadow (APIf rc) _ mem' md'' x HAH' Himg).
    - unfold HIGHMEM_BEG in *; lia.
    - rewrite HERRv; lia.
    - rewrite HOOMv; lia. }
  (* the image's RELRO bytes: frame_facts says the runtime owns none of them *)
  assert (KRELRO : forall a, in_globals AF.frame_RELRO a -> mbyte rsegs mem' a = mbyte rsegs mem1 a).
  { intros a Ha. pose proof (r20_relro_range a Ha) as Hra.
    refine (proj1 (KEEP a _ (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha) (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha)
                     _ _ _ (fun Hc => proj1 (proj2 (proj2 (Hbyte a Hc))) (HRimg a Ha))));
      [lia | unfold HIGHMEM_BEG in *; lia | rewrite HERRv; lia | rewrite HOOMv; lia]. }
  (* the slot window [S - SLOT_STACK, S) stays present and writable *)
  assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct Hwin1 as (Hlo & Hhi & Hw). split; [exact Hlo|]. split; [exact Hhi|].
    intros a Ha. destruct (Z_lt_le_dec a (sp - 4096)) as [Hlt|Hge].
    - destruct (Hw a Ha) as (Hwv & bb & Hmrd).
      destruct (KST a ltac:(lia) ltac:(lia)) as (Hmb & Hwr).
      split; [exact (proj1 Hwr Hwv)|]. exists bb. rewrite <- rh_mbyte_mrd in Hmrd |- *. rewrite Hmb. exact Hmrd.
    - destruct (Z_lt_le_dec a sp) as [Hlt2|Hge2].
      + split.
        * apply Hwinw. unfold AC.a_window. rewrite HKF, Hasp1. lia.
        * destruct (Hwinp a ltac:(unfold AC.a_window; rewrite HKF, Hasp1; lia)) as (bb & Hmb).
          exists bb. rewrite <- rh_mbyte_mrd. exact Hmb.
      + destruct (Hw a Ha) as (Hwv & bb & Hmrd).
        destruct (KST a ltac:(lia) ltac:(lia)) as (Hmb & Hwr).
        split; [exact (proj1 Hwr Hwv)|]. exists bb. rewrite <- rh_mbyte_mrd in Hmrd |- *. rewrite Hmb. exact Hmrd. }
  (* the freed block is the touched region: below stklo, off the image and off the entry blocks *)
  assert (HTO : forall a, phi <= a < phi + rnb g 0 ->
            app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a).
  { intros a Ha. destruct (Hbyte a Ha) as (Happ & _ & Himg_a & _).
    split; [exact Happ|]. split; [lia|]. split; [exact Himg_a|].
    intros (p & n & Hinp & Hr).
    destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem1 md1 phi (rnb g 0) p n HAH1 Hinp)
      as [Hd|Hd]; lia. }
  (* the input block: an entry block, below stklo, off the image, apart from the freed block *)
  assert (KIN : forall x, g_p g <= x < g_p g + g_n g ->
            mbyte rsegs mem' x = mbyte rsegs mem1 x /\
            mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem1 (shadow_addr x)).
  { intros x Hx. destruct (Hinap x Hx) as (Hxa & Hxlo & Hxfr & Hxni).
    assert (Hn0 : 0 < g_n g) by lia.
    destruct (Hinblk1 Hn0) as (HinH & _).
    assert (Hib1 : AC.in_blocks (hb1 phi (rnb g 0) ++ g_H g) x)
      by (exists (g_p g), (g_n g); split; [apply in_or_app; right; exact HinH | lia]).
    assert (Hib2 : AC.in_blocks ([] ++ g_H g) x) by (exists (g_p g), (g_n g); split; [exact HinH | lia]).
    destruct (lw_not_owned (APIf rc) _ mem1 md1 x HAH1 (or_introl Hib1)) as [N1 N2].
    destruct (lw_not_owned (APIf rc) _ mem' md'' x HAH' (or_introl Hib2)) as [N3 N4].
    assert (Hdj : g_p g + g_n g <= phi \/ phi + rnb g 0 <= g_p g)
      by (destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem1 md1 phi (rnb g 0) (g_p g) (g_n g) HAH1 HinH)
            as [Hd|Hd]; [right | left]; lia).
    assert (Hx0 : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
    split.
    - refine (proj1 (KEEP x Hx0 N1 N3 _ _ _ _)).
      + unfold HIGHMEM_BEG in *; lia.
      + intro He. exact (Hxni (errno_in_img x He)).
      + intro He. apply Hxni. rewrite He. exact oom_in_img.
      + lia.
    - pose proof (shadow_of_app x Hxa) as Hsx. pose proof (in_shadow_range _ Hsx) as Hsr.
      pose proof Hsx as Hsx'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsx'.
      refine (proj1 (KEEP _ _ N2 N4 _ _ _ (NBLKsh _ Hsx))).
      + lia.
      + unfold HIGHMEM_BEG in *; lia.
      + rewrite HERRv; lia.
      + rewrite HOOMv; lia. }
  (* ENT at the exit *)
  assert (HENT' : ENT APIf g [] mem' md'').
  { eapply ent_call; [exact HENT1 | exact HFRA1 | exact Hcp | rewrite HKF, HFN; lia | exact HTO | exact Herrk]. }
  assert (HA9 : forall A0, getr regs1 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> A0 = A).
  { intros A0 HA0 HA0r. rewrite E9 in HA0. exact (rh_rg9_eq regs A A0 Hr9 HA0 HA64 HA0r). }
  (* FRA at the exit *)
  assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md'').
  { apply (sl_mid B APIf ra g fr (hb1 phi (rnb g 0)) [] regs1 mem1 md1 regs' mem' md''
             (fun a => phi <= a < phi + rnb g 0) AC.AK_FREE HFRA1 Hcp).
    - cbn. lia.
    - (* sink_none mem' md'' *)
      destruct Hsn1 as ((Hthrm & Hlockm) & Hohd & Hfd).
      split; [split|split].
      + eapply YI14.val_mem_frame; [|exact Hthrm].
        intros x Hx. rewrite Hthr in Hx. cbn in Hx. try rewrite SEGS.
        apply KCL; [lia | apply r20_client_a; lia | exact (r20_img_cov_in 0x5fc8e1 0x5fc8e2 x r20_sink_cov_a ltac:(lia))].
      + eapply YI14.val_mem_frame; [|exact Hlockm].
        intros x Hx. rewrite Hlock in Hx. cbn in Hx. try rewrite SEGS.
        apply KCL; [lia | apply r20_client_b; lia | exact (r20_img_cov_in 0x5fcd40 0x5fcd50 x r20_sink_cov_b ltac:(lia))].
      + intros k Hk. pose proof (Hohd k Hk) as Hk'.
        try rewrite SEGS in Hk'. try rewrite SEGS.
        rewrite KCL.
        * exact Hk'.
        * rewrite Hhead. lia.
        * apply r20_client_b. rewrite Hhead. lia.
        * eapply r20_img_cov_in; [exact r20_sink_cov_b | rewrite Hhead; lia].
      + destruct Hmod as (lz & mt & vm' & Emd). rewrite Emd. exact Hfd.
    - (* G_img_c mem' (RELRO) *)
      intros a Hin. pose proof (Hgimg1 a Hin) as E. rewrite SEGS in E |- *. rewrite <- E.
      exact (KRELRO a Hin).
    - unfold q64 in *. apply (r20_bkeep mem1 mem'); [|exact Hhdr1_1].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - unfold q64 in *. apply (r20_bkeep mem1 mem'); [|exact Hhdr2_1].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - intros A0 HA0 HA0r. rewrite (HA9 A0 HA0 HA0r).
      unfold q64 in *. apply (r20_bkeep mem1 mem'); [|exact Hspill1].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(unfold APPMEM_END in *; lia) ltac:(lia))).
    - intros A0 HA0 HA0r v Hv. rewrite (HA9 A0 HA0 HA0r) in Hv |- *.
      unfold q64 in *. apply (r20_bkeep mem1 mem'); [|exact Hv].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(unfold APPMEM_END in *; lia) ltac:(lia))).
    - intros A0 HA0 HA0r. rewrite (HA9 A0 HA0 HA0r).
      unfold q64 in *. apply (r20_bkeep mem1 mem'); [|exact Hfr56_1].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(unfold APPMEM_END in *; lia) ltac:(lia))).
    - destruct Hsh1 as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
      apply (r20_bkeep mem1 mem'); [|exact Hshb]. rewrite Hshl. intros x Hx.
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr))) by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
      apply KFRsh. lia.
    - apply (r20_bkeep mem1 mem'); [|exact Hsaved1]. intros x Hx.
      unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      exact (proj1 (KST x ltac:(unfold APPMEM_END in *; lia) ltac:(lia))).
    - exact HWIN'.
    - intros a Hin. apply (r20_addr_keep mem1 mem' a 1 (HAG1 a Hin)).
      intros i Hi. replace (a + i) with a by lia. exact (KIMGsh a (r20_ag_img a Hin)).
    - intros a Hwa Hnf. apply (r20_addr_keep mem1 mem' a 1 (HWA1 a Hwa Hnf)).
      intros i Hi. replace (a + i) with a by lia.
      pose proof (HWA1 a Hwa Hnf) as (_ & _ & _ & Hab). destruct (Hab 0 ltac:(lia)) as (Hap & _).
      rewrite Z.add_0_r in Hap.
      apply KSH; [left; unfold AF.SLOT_STACK in *; lia | exact Hap].
    - (* FSREC: the tp word is kept; the flag byte and the slot's last word are side-stack bytes *)
      intros (FS & j & Htp & HFSr & Hj & Hfrj & Hflag & Htail).
      destruct (lw_fs_place (APIf rc) _ mem1 md1 FS HAH1 Htp HFSr) as [_ HFSlo _ _].
      assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
      assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
      assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
      assert (Hj' : 0 <= j < 256) by (rewrite <- HM6; exact Hj).
      assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfrj; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
      assert (KFS : forall a, FS <= a < FS + AC.FS_SIZE -> mbyte rsegs mem' a = mbyte rsegs mem1 a).
      { intros a Ha.
        assert (Hfsa : AC.a_in_fs AC.ASYMS mem1 a)
          by (exists FS; split; [exact HFSr | split; [exact Htp | exact Ha]]).
        destruct (FSC a ltac:(lia) Hfsa) as (Hga & _).
        refine (proj1 (KLOC a (or_intror (conj Hfsa Hga)) _ _)); [lia|].
        intro Hb. exact (Hbnfs a Hb Hfsa). }
      exists FS, j.
      split; [intros k Hk; rewrite (Htp16 (Z.of_nat k) ltac:(lia)); exact (Htp k Hk)|].
      split; [exact HFSr|]. split; [exact Hj|]. split; [exact Hfrj|].
      split.
      + apply (r20_bkeep mem1 mem'); [|exact Hflag]. cbn [length]. intros x Hx. apply KFS. lia.
      + apply (r20_bkeep mem1 mem'); [|exact Htail]. rewrite length_le8. intros x Hx. apply KFS.
        rewrite HB6 in Hx. lia.
    - apply (r20_bkeep mem1 mem'); [|exact Hinb1]. intros x Hx.
      exact (proj1 (KIN x ltac:(unfold g_n, nlen; lia))).
    - intros Hn. destruct (Hinblk1 Hn) as (_ & Had).
      apply (r20_addr_keep mem1 mem' (g_p g) (g_n g) Had). intros i Hi. exact (proj2 (KIN (g_p g + i) ltac:(lia))).
    - exact F2.
    - exact F3.
    - exact F4.
    - exact F8.
    - exact F9.
    - exact F19.
    - exact F26. }
  (* RBE at the exit *)
  assert (HRBE' : RBE g fr regs' mem').
  { destruct HRBE1 as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
      S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA & HA2176 & HNM & HOURa & HTBL & HBOX & HMROW &
      HPRA & S152 & S112 & HA2256 & S160).
    assert (KSP : forall off w, 0 <= off -> off + 8 <= 448 -> spill regs1 mem1 off w -> spill regs' mem' off w).
    { intros off w Ho0 Ho1 Hs.
      pose proof (rh_spill_at regs1 mem1 A off w Hs ltac:(unfold rg in *; rewrite E9; exact Hr9) ltac:(lia) HA4
                    Ho0 Ho1) as Hq.
      exists A. split; [unfold rg in *; rewrite F9, E9; exact Hr9|].
      unfold q64 in *. apply (r20_bkeep mem1 mem'); [|exact Hq].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(unfold APPMEM_END in *; lia) ltac:(lia))). }
    assert (Hrodx : forall x, 0x21000 <= x < 0x22000 -> ro_addr rsegs (wa x) = true)
      by (intros x Hx; exact (r20_ro_run_ok _ _ r20_rod_ro x ltac:(cbn; lia))).
    pose proof (rb_mrow_range (g_in g)) as (Hmr0 & Hmr1 & _).
    unfold RBE.
    do 21 (split; [apply KSP; [lia | lia | assumption]|]).
    split.
    { unfold OUTA in *. apply (r20_addr_keep mem1 mem' _ _ HOUTA). intros i Hi. apply KFRsh. lia. }
    split.
    { apply (r20_addr_keep mem1 mem' _ _ HA2176). intros i Hi. apply KFRsh. lia. }
    split.
    { intros Hc. destruct (HNM Hc) as (Hok & Hbytes & Haddr & Hpos & Hhi).
      (* the row name: rodata bytes of the image, in [0x21000, 0x22000) *)
      pose proof (r20_name_rng (g_in g) Hc) as Hnr.
      split; [exact Hok|].
      split.
      { apply (r20_ro_bytes mem1 mem' _ _ Hro1 Hro' ); [|exact Hbytes].
        intros x Hx. apply Hrodx. pose proof (Hnr (x - RcSynth.rname (rt_mb (g_in g))) ltac:(lia)). lia. }
      split.
      { apply (r20_addr_keep mem1 mem' _ _ Haddr). intros i Hi. apply KIMGsh.
        apply (r20_img_cov_in 0x21000 0x22000 _ r20_rod_cov). exact (Hnr i Hi). }
      split; [exact Hpos | exact Hhi]. }
    split.
    { apply (r20_addr_keep mem1 mem' _ _ HOURa). intros i Hi. apply KFRsh. lia. }
    split.
    { apply (r20_bkeep mem1 mem'); [|exact HTBL]. intros x Hx. apply KRELRO.
      exists 0x9f168, 9344. split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity|].
      unfold BAC.BA_FR in Hx. assert (Hl : length BAP.ba_tbl = 168%nat) by (vm_compute; reflexivity).
      rewrite Hl in Hx. cbn in Hx. lia. }
    split.
    { apply (r20_ro_bytes mem1 mem' _ _ Hro1 Hro'); [|exact HBOX].
      intros x Hx. apply Hrodx. unfold BOXA, box6 in Hx. cbn in Hx. lia. }
    split.
    { apply (r20_bkeep mem1 mem'); [|exact HMROW]. intros x Hx. apply KRELRO.
      exists 0x9f168, 9344. split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity|].
      rewrite rb_mb_len in Hx. unfold CAT in *. lia. }
    split.
    { unfold PRA in *. destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
      do 10 (split; [apply KSP; [lia | lia | assumption]|]). apply KSP; [lia | lia | assumption]. }
    split; [apply KSP; [lia | lia | exact S152]|].
    split; [apply KSP; [lia | lia | exact S112]|].
    split; [apply (r20_addr_keep mem1 mem' _ _ HA2256); intros i Hi; apply KFRsh; lia|].
    apply KSP; [lia | lia | exact S160]. }
  (* the exit cut *)
  rewrite <- SEGS. apply Hexit.
  exists regs', mem', md'', fr.
  split; [reflexivity|].
  split; [exact HFRA'|].
  split; [exact HENT'|].
  pose proof HRB1 as (_ & HCUR1 & HOUR1 & H22_1 & HIDB1 & HFGB1).
  split; [exact Hgn|].
  split; [lia|].
  split; [unfold rg in *; rewrite F22; exact H22_1|].
  split.
  { unfold OURb in *. apply (r20_bkeep mem1 mem'); [|exact HOUR1]. rewrite OUR_length. intros x Hx.
    apply KFR. lia. }
  split; [exact HRBE'|].
  split; [unfold rg in *; rewrite F21, E21; exact H21|].
  assert (ERID : RID (g_in g) 1 = RID (g_in g) 0) by (unfold RID; rewrite r20_st1; reflexivity).
  assert (ERFG : RFG (g_in g) 1 = RFG (g_in g) 0) by (unfold RFG; rewrite r20_st1; reflexivity).
  rewrite ERID, ERFG.
  split; [|unfold rg; rewrite F27, E27; exact H27].
  split; [lia|].
  split.
  { destruct HCUR1 as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
    split; [exact Hc0|]. split; [rewrite F23; exact Hc23 | rewrite F25; exact Hc25]. }
  split.
  { unfold OURb in *. apply (r20_bkeep mem1 mem'); [|exact HOUR1]. rewrite OUR_length. intros x Hx.
    apply KFR. lia. }
  split; [unfold rg in *; rewrite F22; exact H22_1|].
  split.
  { unfold IDBr in *. apply (r20_bkeep mem1 mem'); [|exact HIDB1]. rewrite (rb_RID_len (g_in g) 0).
    intros x Hx. apply KFR. lia. }
  { unfold FGBr in *. apply (r20_bkeep mem1 mem'); [|exact HFGB1]. rewrite (rb_RFG_len (g_in g) 0 ltac:(lia)).
    intros x Hx. apply KFR. lia. }
Qed.

End S.
