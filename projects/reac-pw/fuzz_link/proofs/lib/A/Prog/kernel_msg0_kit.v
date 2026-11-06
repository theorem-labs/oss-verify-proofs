(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 494 of its 550 lines of code are new or changed and 1249 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the kit of kernel's message set-up (kernel_msg0_a.v, _b.v, _c.v, kernel_msg0.v): what
   the message path's set-up needs beside kernel_defs.v and kernel_kit.v (whose kn_ lemmas give the call's numbers, the
   read set's places, its shadow at a cut and the cut's frame):
   - the symbolic states of the lane's runs (km_ssA at +0x594, km_ssZ at +0x1e7c, km_ssB at +0x5b4 / +0x1e8c) and
     their env km_E, with the cursor's shadow entry (km_shok) and the atom facts (km_facts);
   - the two calls of the set-up as lemmas over kernel's facts (km_call_mf: meta_fill_00 on w2's shadow, LinkWalkSide.v
     aj_gx_set_shadow_at; km_call_ms: checked_memset of w2, link_ajkit.v aj_gx_intrin_at) and the cuts after them
     (km_land_mf, km_land_ms: kernel_kit.v kat_frame, with F's shadow and the slot KS_CI restated);
   - the lane's own cuts at +0x5b4 (kin_m5b4), +0x5c4 (kin_m5c4) and +0x1e8c (kin_z1e8c).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import attr_text_c nl_error_c kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- byte-level helpers (no image) ---- *)

(* ---- the symbolic states of the lane's runs (atoms 0..31: the registers; 32 = p, 33 = n: the cursor's words;
   34 = shadow(w2) = shadow(F) + 0x226) ---- *)
Definition km_Bx : sv := SOff 20 0.
Definition km_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address (x + c >> 3) + s4 *)
Definition km_sh (r : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff r c) (SLit 3)) (SOff 20 0).
Definition km_atoms : list (nat * afact) :=
  [(18%nat, mkAF 0 (2 ^ 47 - 16) 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
(* +0x594: the cursor (read only), the slots 0x58 (NW_SIZE) and 0x80 (shadow(w2)), the slot 0x78 written *)
Definition km_curA : YP09.region :=
  YP09.mkRegion (Some 18%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition km_slA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x58 0x88 0x78 0x80
    [YP09.mkChunk 0x58 (CVal 8 (SLit 4112)); YP09.mkChunk 0x80 (CVal 8 (SOff 34 0))].
(* s3 = a0 + 8, s8 = shadow(a0 + 8), as the engine's address forms *)
Definition km_regsA : list sv := sr_set (sr_set sr_atoms (Z_to_bv 5 19) (SOff 18 8)) (Z_to_bv 5 24) (km_sh 18 8).
Definition km_ssA : sstate := mkSS (kpc KP_MSG0) km_regsA [km_curA; km_slA] None (mkFacts km_atoms [] []).
Definition km_SHA : list shent := [mkSHE 18 0 16].
(* +0x1e7c: the slot 0x80 read, the slot 0x78 written *)
Definition km_slZ : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x78 0x88 0x78 0x80 [YP09.mkChunk 0x80 (CVal 8 (SOff 34 0))].
Definition km_ssZ : sstate := mkSS (kpc KP_MZ) sr_atoms [km_slZ] None (mkFacts km_atoms [] []).
(* +0x5b4, +0x1e8c: the slot 0x58 read *)
Definition km_slB : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0 0 [YP09.mkChunk 0x58 (CVal 8 (SLit 4112))].
Definition km_ssB (pc : Z) : sstate := mkSS (kpc pc) sr_atoms [km_slB] None (mkFacts km_atoms [] []).
(* the registers a run keeps: the callee-saved ones *)
Definition km_csz : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma km_pres : forall (rg rg2 : bvmap 5 word) (r : bv 5), aregs_preserved rg rg2 ->
  existsb (Z.eqb (bv_unsigned r)) km_csz = true -> getr rg2 r = getr rg r.
Proof.
  intros rg rg2 r HP Hr. apply existsb_exists in Hr as (z & Hz & Hq). apply Z.eqb_eq in Hq.
  assert (Hc : acallee_saved (bv_unsigned r)).
  { unfold acallee_saved. rewrite Hq. cbn [km_csz In] in Hz. lia. }
  pose proof (HP _ Hc) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

Lemma km_div8 : forall f y, f mod 8 = 0 -> (f + y) / 8 = f / 8 + y / 8.
Proof.
  intros f y H. rewrite (Z.div_mod f 8) at 1 by lia. rewrite H, Z.add_0_r, Z.mul_comm.
  rewrite Z.div_add_l by lia. reflexivity.
Qed.

(* membership in a literal list *)
Ltac km_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma km_cs_bv : forall r, existsb (Z.eqb (Z.of_nat r)) km_csz = true ->
  existsb (Z.eqb (bv_unsigned (Z_to_bv 5 (Z.of_nat r)))) km_csz = true.
Proof.
  intros r H. apply existsb_exists in H as (z & Hz & Hq). apply Z.eqb_eq in Hq. rewrite Hq.
  cbn [km_csz In] in Hz. repeat (destruct Hz as [<- | Hz]; [vm_compute; reflexivity |]). destruct Hz.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.     (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis AS00 : aset_shadow_realizes pa_segs B 0x55e74 0x00.        (* meta_fill_00: SetShadow.v link_set_shadow_00 *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.         (* checked_memset: AE2r.v asan_memset_realizes *)
#[local] Notation SEGS := (pa_segs).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- F's shadow bytes, one at a time ---- *)
Lemma kfsh_w2z : forall s1v r i, 0x226 <= i < 0x428 -> nth (Z.to_nat i) (kfsh s1v 0 r) 0 = 0.
Proof.
  intros s1v r i Hi. rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec (Z.to_nat i) 4); [lia|]. destruct (Nat.ltb_spec (Z.to_nat i) 0x206); [lia|].
  destruct (Nat.ltb_spec (Z.to_nat i) 0x226); [lia|]. destruct (Nat.ltb_spec (Z.to_nat i) 0x428); [reflexivity | lia].
Qed.

Lemma km_sh_at : forall cx fpos W3 ms3 sh i, kshadow cx fpos W3 ms3 sh -> 0 <= i < Z.of_nat (length sh) ->
  aview SEGS (w_H W3) (ms_mem ms3) (kFSH cx fpos + i) = Some (nth (Z.to_nat i) sh 0).
Proof.
  intros cx fpos W3 ms3 sh i H Hi. rewrite <- (Z2Nat.id i) at 1 by lia. apply H. lia.
Qed.

(* ---- the frame addresses of a cut's layout are the call's (both journals start at the call's layout) ---- *)
Lemma km_fa : forall cx fpos k2 ly3 S3 W3 mm md3, kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  forall cid pos, frame_addr ly3 cid pos = frame_addr (k_lyc cx) cid pos.
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md3 HB HJ3 cid pos. pose proof HB as ((HJ0 & _) & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & Hly0 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (_ & Hly3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  unfold frame_addr. rewrite EF0, EF3. reflexivity.
Qed.

(* ---- two edits of a cut: its F shadow list, more slots ---- *)
Lemma km_kat_sh : forall cx fpos pc rl sl sh sh' live adv g k2 ly3 S3 W3 ms3 md3,
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 -> kshadow cx fpos W3 ms3 sh' ->
  kat B cx fpos pc rl sl sh' live adv g k2 ly3 S3 W3 ms3 md3.
Proof.
  intros cx fpos pc rl sl sh sh' live adv g k2 ly3 S3 W3 ms3 md3
    (H1 & H2 & H3 & H4 & H5 & _ & H7 & H8 & H9 & H10 & H11 & H12) Hsh.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj Hsh (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 H12))))))))))).
Qed.

Lemma km_kat_sl : forall cx fpos pc rl sl sl2 sh live adv g k2 ly3 S3 W3 ms3 md3,
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 -> kslots_eq cx W3 ms3 sl2 ->
  kat B cx fpos pc rl (sl ++ sl2) sh live adv g k2 ly3 S3 W3 ms3 md3.
Proof.
  intros cx fpos pc rl sl sl2 sh live adv g k2 ly3 S3 W3 ms3 md3
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hsl.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj _ (conj H8 (conj H9 (conj H10
    (conj H11 H12))))))))))).
  unfold kslots_eq in *. apply Forall_app. split; assumption.
Qed.

(* ---- the cut after meta_fill_00 on w2's shadow: the step changed the slot KS_CI and w2's 0x202 shadow bytes ---- *)
Lemma km_land_mf : forall cx fpos pc rl sl adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' ci,
  kbase SK B cx ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0xf8 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  (forall ov, In ov sl -> 0x18 <= fst ov <= 0xf0 /\ (fst ov + 8 <= KS_CI \/ KS_CI + 8 <= fst ov)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ksp1 cx + KS_CI <= a < ksp1 cx + KS_CI + 8) ->
     ~ (kFSH cx fpos + 0x226 <= a < kFSH cx fpos + 0x428) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall i, 0 <= i < 0x202 -> aview SEGS (w_H W3) (ms_mem ms') (kFSH cx fpos + 0x226 + i) = Some 0) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms')) (ksp1 cx + KS_CI) = Some ci ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' ->
  kat B cx fpos pc' rl' (sl ++ [(KS_CI, ci)]) (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc rl sl adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' ci HB HK Hsl UN H00 Hci HP Hfds Hfs
    Hkms Hr0 Hrl.
  pose proof HK as (_ & _ & _ & _ & _ & HSH & _ & HJB & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _ & S6 & S7 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity.
  rewrite kn_fsb8 in F2, F3, F5.
  assert (Hf8 : kF cx fpos / 8 <= 2 ^ 44 - 2048) by (apply Z.div_le_upper_bound; lia).
  assert (Hf0 : 512 <= kF cx fpos / 8) by (apply Z.div_le_lower_bound; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  set (X := fun a => (ksp1 cx + KS_CI <= a < ksp1 cx + KS_CI + 8) \/
                     (kFSH cx fpos + 0x226 <= a < kFSH cx fpos + 0x428)).
  assert (UNX : forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
            aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hx. apply UN; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H]. }
  assert (HK0 : kat B cx fpos pc rl sl [] true adv g k2 ly3 S3 W3 ms3 md3).
  { apply (km_kat_sh cx fpos pc rl sl _ [] true adv g k2 ly3 S3 W3 ms3 md3 HK). intros i Hi. cbn in Hi. lia. }
  assert (HXin : forall a, X a -> kX_in cx fpos a).
  { intros a [Ha | Ha]; unfold kX_in.
    - right. right. right. unfold KS_CI in Ha. rewrite HK8. lia.
    - right. right. left. rewrite kn_fsb8. change (16384 / 8) with 2048. lia. }
  assert (HXm : kX_miss cx fpos sl (Z.of_nat (length (@nil Z))) X).
  { unfold kX_miss, X, kFSH, shadow_of_addr, SHADOW_OFF, KS_CI. cbn [length Z.of_nat].
    rewrite kn_fsb8.
    split; [intros a Ha [H|H]; lia|].
    split.
    { intros ov Hov. destruct (Hsl ov Hov) as ((Ho1 & Ho2) & Ho3). unfold KS_CI in Ho3.
      split; [lia|]. intros a Ha [H|H]; lia. }
    split; [intros a Ha [H|H]; lia|].
    split; [intros a Ha [H|H]; lia|].
    split; [intros a Ha; lia|].
    split.
    { intros a Ha. assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in Ha; exact Ha).
      destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB Hx) as (L1 & L2 & _ & L4).
      unfold kLowMemEnd, kHighMemBeg in L2. rewrite HK8 in L4. intros [H|H]; lia. }
    split; [intros a Ha; unfold LA_G_NL, NK_SIZE in Ha; intros [H|H]; lia|].
    intros a Ha; unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Ha; intros [H|H]; lia. }
  pose proof (kat_frame SK B LAWS X cx fpos pc rl sl [] true adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl W3 ms' md'
    HB HK0 Hkms Hr0 Hrl (incl_refl sl) ltac:(cbn; lia) Hfds Hfs UNX HP HXin HXm) as HK1.
  apply (km_kat_sh cx fpos pc' rl' (sl ++ [(KS_CI, ci)]) [] (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms' md').
  - apply km_kat_sl; [exact HK1|]. unfold kslots_eq. apply Forall_cons; [cbn [fst snd]; exact Hci | apply Forall_nil].
  - apply (kn_kshadow_w2 cx fpos W3 ms3 ms' 0xf8 0xf8 0xf3 HSH); [|exact H00].
    intros i Hi Hn. apply UN; unfold kFSH, shadow_of_addr, SHADOW_OFF, KS_CI in *; lia.
Qed.

(* ---- the cut after checked_memset(w2, 0, 4112): the step changed w2 and the callee's window ---- *)
Lemma km_land_ms : forall cx fpos pc rl sl adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl',
  kbase SK B cx ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  (forall ov, In ov sl -> 0x18 <= fst ov <= 0xf0) ->
  (forall i, 0 <= i < NW_SIZE -> aview SEGS (w_H W3) (ms_mem ms') (kW2 cx fpos + i) = Some 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) -> ~ (ksp1 cx - ESTACK <= a < ksp1 cx) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' ->
  kw_at W3 ms' (kW2 cx fpos) 0 0 /\
  kat B cx fpos pc' rl' sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc rl sl adv g k2 ly3 S3 W3 ms3 md3 ms' md' pc' rl' HB HK Hsl H0s UN HP Hfds Hfs Hkms Hr0 Hrl.
  pose proof HK as (_ & _ & _ & _ & HFR & _ & _ & HJB & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _ & S6 & S7 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity.
  assert (HES : ESTACK = 4096) by reflexivity.
  rewrite kn_fsb8 in F2, F3, F5.
  assert (Hf8 : kF cx fpos / 8 <= 2 ^ 44 - 2048) by (apply Z.div_le_upper_bound; lia).
  assert (Hf0 : 512 <= kF cx fpos / 8) by (apply Z.div_le_lower_bound; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  split.
  { apply kn_kw_zero; [unfold kW2, KN_W2; lia | unfold kW2, KN_W2, NW_SIZE; lia | exact H0s |].
    intros i Hi. apply HP. destruct HFR as (_ & _ & _ & _ & Hpf & _). apply Hpf. rewrite kn_fsb8.
    unfold kW2, KN_W2, NW_SIZE in *. lia. }
  set (X := fun a => (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) \/ (ksp1 cx - ESTACK <= a < ksp1 cx)).
  apply (kat_frame SK B LAWS X cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 pc' rl' sl W3 ms' md'
    HB HK Hkms Hr0 Hrl (incl_refl sl) ltac:(rewrite kfsh_length; lia) Hfds Hfs).
  - intros a Ha Hx. apply UN; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H].
  - exact HP.
  - intros a [Ha | Ha]; unfold kX_in.
    + right. left. rewrite kn_fsb8. unfold kW2, KN_W2, NW_SIZE in Ha. lia.
    + right. right. right. rewrite HK8. rewrite HES in Ha. lia.
  - unfold kX_miss, X, kW2, KN_W2, NW_SIZE, kFSH, shadow_of_addr, SHADOW_OFF. rewrite kfsh_length, kn_fsb8, HES.
    change (Z.of_nat 0x448) with 0x448.
    split; [intros a Ha [H|H]; lia|].
    split.
    { intros ov Hov. pose proof (Hsl ov Hov) as Ho. split; [lia|]. intros a Ha [H|H]; lia. }
    split; [intros a Ha [H|H]; lia|].
    split; [intros a Ha [H|H]; lia|].
    split; [intros a Ha [H|H]; lia|].
    split.
    { intros a Ha. assert (Hx : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (left; unfold ka0 in Ha; exact Ha).
      destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB Hx) as (L1 & L2 & L3 & L4).
      rewrite HK8 in L4. intros [H|H]; lia. }
    split; [intros a Ha; unfold LA_G_NL, NK_SIZE in Ha; intros [H|H];
            unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5; lia|].
    intros a Ha; unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Ha; intros [H|H];
      unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5; lia.
Qed.

(* ---- the env of a run's start: the registers, then p, n, shadow(w2) ---- *)
Definition km_E (ms : machine_state) (p n w : Z) : env := Eimg (Ereg (ms_regs ms) [w64 p; w64 n; w64 w]).

Lemma km_E_reg : forall ms p n w (jj : nat) (r : bv 5), Z.of_nat jj = bv_unsigned r ->
  ew (km_E ms p n w) jj = getr (ms_regs ms) r.
Proof. intros ms p n w jj r H. unfold km_E. apply ew_Eimg_Ereg_nat. exact H. Qed.

Lemma km_E_ext : forall ms p n w,
  ew (km_E ms p n w) 32%nat = w64 p /\ ew (km_E ms p n w) 33%nat = w64 n /\ ew (km_E ms p n w) 34%nat = w64 w.
Proof.
  intros ms p n w. unfold km_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
  split; [exact (ew_Ereg_extra _ _ 0) | split; [exact (ew_Ereg_extra _ _ 1) | exact (ew_Ereg_extra _ _ 2)]].
Qed.

Lemma km_E_agree : forall ms p n w, YP06.env_agree 32 (Ereg (ms_regs ms) [w64 p; w64 n; w64 w]) (km_E ms p n w).
Proof. intros ms p n w. unfold km_E. split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* the registers kregs0 names, in the env *)
Lemma km_E0 : forall cx ms3 p n w, kregs0 cx ms3 ->
  ew (km_E ms3 p n w) 18%nat = w64 (ka0 cx) /\ ew (km_E ms3 p n w) 9%nat = w64 (ksp1 cx) /\
  ew (km_E ms3 p n w) 20%nat = w64 SHADOW_OFF /\ ew (km_E ms3 p n w) 2%nat = w64 (ksp1 cx).
Proof.
  intros cx ms3 p n w (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  split; [rewrite (km_E_reg ms3 p n w 18 18%bv eq_refl); exact R18|].
  split; [rewrite (km_E_reg ms3 p n w 9 9%bv eq_refl); exact R9|].
  split; [rewrite (km_E_reg ms3 p n w 20 20%bv eq_refl); exact R20|].
  rewrite (km_E_reg ms3 p n w 2 2%bv eq_refl); exact R2.
Qed.

Lemma km_bv : forall (E : env) (nn : nat) v, ew E nn = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E nn) = v.
Proof. intros E nn v H Hv. rewrite H. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* the cursor: an application byte range below 2 ^ 47, off kernel's window *)
Lemma km_cur_loc : forall cx fpos k2 ly3 S3 md3, kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  0 <= ka0 cx /\ ka0 cx + 16 <= 2 ^ 47 /\
  (forall x, ka0 cx <= x < ka0 cx + 16 ->
     (x < kLowMemEnd \/ kHighMemBeg <= x) /\ ~ (ksp cx - KERNEL_AK <= x < ksp cx)).
Proof.
  intros cx fpos k2 ly3 S3 md3 HB HJB.
  assert (H : forall x, ka0 cx <= x < ka0 cx + 16 -> kernel_ard SEGS (k_regs cx) (km0 cx) x)
    by (intros x Hx; left; unfold ka0 in Hx; exact Hx).
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx) HB HJB (H (ka0 cx) ltac:(lia))) as (L0 & _).
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx + 15) HB HJB (H (ka0 cx + 15) ltac:(lia))) as (L15 & _).
  split; [lia|]. split; [lia|].
  intros x Hx. destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 x HB HJB (H x Hx)) as (_ & L2 & _ & L4).
  split; [exact L2 | exact L4].
Qed.

Lemma km_facts : forall cx fpos k2 ly3 S3 md3 (E : env), kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  ew E 18%nat = w64 (ka0 cx) -> ew E 9%nat = w64 (ksp1 cx) -> ew E 20%nat = w64 SHADOW_OFF ->
  facts_ok E (mkFacts km_atoms [] []).
Proof.
  intros cx fpos k2 ly3 S3 md3 E HB HJB E18 E9 E20.
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & _).
  destruct (km_cur_loc cx fpos k2 ly3 S3 md3 HB HJB) as (C0 & C16 & _).
  pose proof asan_consts as ((C1a & C1b) & _). assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1.
  unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
  unfold km_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, E9, E20. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; first [lia | exact I | exact S5].
Qed.

(* the cursor's shadow entry at a cut *)
Lemma km_shok : forall cx fpos k2 ly3 S3 W3 ms3 md3 (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 -> kkept B cx fpos W3 ms3 ->
  ew E 18%nat = w64 (ka0 cx) -> ew E 20%nat = w64 SHADOW_OFF ->
  sh_ok SEGS km_Bx km_SHA E (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20.
  destruct (km_cur_loc cx fpos k2 ly3 S3 md3 HB HJB) as (C0 & C16 & CL).
  apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold km_Bx.
  rewrite (U_atom _ 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 18 (ka0 cx) E18) by lia.
  split.
  - rewrite <- (aview_rd_of SEGS). rewrite Z.add_0_r. replace (16 - 0) with 16 by lia.
    exact (kn_cursor_ra SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HJB HKK).
  - intros a Ha. change (Z.min 0 16) with 0 in Ha. change (Z.max 0 16) with 16 in Ha.
    destruct (CL a ltac:(lia)) as ([Hq | Hq] & _); unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* ---- words of a region ---- *)
Lemma km_rdword_range : forall (H : word -> bool) (m : word -> option byte) a v,
  rdword (aview SEGS H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H m a v Hv.
  assert (R : forall x b, aview SEGS H m x = Some b -> 0 <= b < 256).
  { intros x b Hb. destruct (aview_byte SEGS H m x b Hb) as (_ & _ & _ & Hr). exact Hr. }
  unfold rdword in Hv.
  destruct (aview SEGS H m a) as [b0|] eqn:E0; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 1)) as [b1|] eqn:E1; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 2)) as [b2|] eqn:E2; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 3)) as [b3|] eqn:E3; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 4)) as [b4|] eqn:E4; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 5)) as [b5|] eqn:E5; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 6)) as [b6|] eqn:E6; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 7)) as [b7|] eqn:E7; [|cbv iota beta in Hv; discriminate Hv].
  cbv iota beta in Hv. injection Hv as <-.
  apply R in E0. apply R in E1. apply R in E2. apply R in E3.
  apply R in E4. apply R in E5. apply R in E6. apply R in E7. lia.
Qed.

Lemma km_chunk_rd : forall E (H : word -> bool) (mm : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> rdword (aview SEGS H mm) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mm) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H mm base off e v He Hr.
  pose proof (km_rdword_range H mm (base + off) v Hr) as Hv.
  apply (chunk_ok_val SEGS E (mrestrict H mm) base off 8 e v He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
  - exact (val_mem_of_rdword SEGS H mm (base + off) v Hr).
Qed.

Lemma km_rd_of_region : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off e v,
  region_ok SEGS E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mm) (b + off) = Some v.
Proof.
  intros E H mm n b cs lo hi wlo whi off e v HR Hb Hin He Hv.
  apply (rdword_of_val_mem SEGS H mm (b + off) v); [|exact Hv].
  apply (field_of_region (segs := SEGS) E (mrestrict H mm) n b cs lo hi wlo whi off 8 e v HR Hb Hin He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
Qed.

(* the registers a run does not write: the same symbolic value at its start and at its end (a call stop) *)
Lemma km_reg_same : forall E ss0 ss1 (H : word -> bool) (ms0 ms1 : machine_state) (l : list Z),
  st_ok_pi SEGS pa_val E ss0 (restrict H ms0) -> st_ok SEGS E ss1 (restrict H ms1) ->
  forallb (fun k => sv_eqb (sr_get (ss_regs ss1) (Z_to_bv 5 k)) (sr_get (ss_regs ss0) (Z_to_bv 5 k))) l = true ->
  forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) l = true -> getr (ms_regs ms1) r = getr (ms_regs ms0) r.
Proof.
  intros E ss0 ss1 H ms0 ms1 l HS0 HS1 Hl r Hr.
  apply existsb_exists in Hr as (k & Hk & Hrk). apply Z.eqb_eq in Hrk.
  rewrite forallb_forall in Hl. pose proof (Hl k Hk) as Hs. apply sv_eqb_eq in Hs.
  assert (Er : r = Z_to_bv 5 k) by (rewrite <- Hrk; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite (st_ok_restrict_reg SEGS H E ss1 ms1 r HS1), (st_ok_pi_restrict_reg H E ss0 ms0 r HS0), Er, Hs.
  reflexivity.
Qed.

(* ---- THE TWO CALLS of the set-up over kernel's facts ---- *)

(* meta_fill_00(shadow(w2), 0x202) from s1 (LinkWalkSide.v aj_gx_set_shadow_at): w2's shadow is F's *)
Lemma km_call_mf : forall cx fpos k2 ly3 S3 W3 mm md3 (rg : bvmap 5 word) raw (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mm md3 k2 ->
  getr rg 10 = w64 (kFSH cx fpos + 0x226) -> getr rg 11 = w64 0x202 -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall i, 0 <= i < 0x202 -> aview SEGS (w_H W3) mem2 (kFSH cx fpos + 0x226 + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (kFSH cx fpos + 0x226 <= a < kFSH cx fpos + 0x226 + 0x202) ->
        aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mm a) ->
     (forall a, apresent (w_H W3) mm a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md3 md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 0x55e74) mm (seg_rom SEGS)) md3) Q.
Proof.
  intros cx fpos k2 ly3 S3 W3 mm md3 rg raw Q HB HJ R10 R11 R2 R3 R4 R1 Hraw CONT.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _ & _ & _ & Hgp & Htp & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (HFA : shadow_addr (frame_addr ly3 KN_CID fpos) = kFSH cx fpos)
    by (rewrite (km_fa cx fpos k2 ly3 S3 W3 mm md3 HB HJ); reflexivity).
  eapply SRr_bind.
  - eapply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low 0x55e74 0 AS00 (k_G cx) (k_XO cx) (k_OUT cx) W3 rg mm
      (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md3 k2
      KN_CID fpos (kFSH cx fpos + 0x226) 0x202 raw HGok HJ);
    [ left; reflexivity | exact R10 | exact R11 | lia | rewrite HFA; lia
    | rewrite HFA, kn_fsb8; change (16384 / 8) with 2048; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw ].
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H00 & Hkeep & Hpres & Hsbm).
    exact (CONT regs2 mem2 md2 HJ2 HP2 H00 Hkeep Hpres Hsbm).
Qed.

(* checked_memset(w2, 0, 4112) from s1 (link_ajkit.v aj_gx_intrin_at): w2 lies in kernel's own side frame F, its
   shadow is 0 (kfsh .. 0 ..) *)
Lemma km_call_ms : forall cx fpos k2 ly3 S3 W3 ms3 md3 (rg : bvmap 5 word) raw (Q : world SEGS -> config -> Prop),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kjbk B cx fpos k2 ly3 S3 md3 ->
  kshadow cx fpos W3 ms3 (kfsh 0xf8 0 0xf3) ->
  getr rg 10 = w64 (kW2 cx fpos) -> getr rg 11 = w64 0 -> getr rg 12 = w64 NW_SIZE -> getr rg 2 = w64 (ksp1 cx) ->
  getr rg 3 = getr (k_regs cx) 3 -> getr rg 4 = getr (k_regs cx) 4 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2,
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 mem2 md2 k2 ->
     aregs_preserved rg regs2 ->
     (forall i, 0 <= i < NW_SIZE -> aview SEGS (w_H W3) mem2 (kW2 cx fpos + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) ->
        ~ (ksp1 cx - ESTACK <= a < ksp1 cx) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) mem2 a) ->
     same_but_materialized md3 md2 ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 0x53214) (ms_mem ms3) (seg_rom SEGS)) md3) Q.
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rg raw Q HB HJ HJB HSH R10 R11 R12 R2 R3 R4 R1 Hraw CONT.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _ & _ & _ & Hgp & Htp & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
  rewrite kn_fsb8 in F2, F3.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  assert (Hsp : spZ rg = ksp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Hw2 : kW2 cx fpos = kF cx fpos + 0x1130) by reflexivity.
  assert (HF8 : (kF cx fpos) mod 8 = 0) by lia.
  assert (HSO8 : SHADOW_OFF mod 8 = 0) by reflexivity.
  assert (HFS8 : kFSH cx fpos mod 8 = 0).
  { unfold kFSH, shadow_of_addr. unfold SHADOW_OFF. lia. }
  (* the shadow byte of a byte of w2 *)
  assert (Hsh8 : forall x, kW2 cx fpos <= x < kW2 cx fpos + NW_SIZE ->
            shadow_of_addr SHADOW_OFF x = kFSH cx fpos + (0x226 + (x - kW2 cx fpos) / 8)).
  { intros x Hx. unfold kFSH, shadow_of_addr.
    replace x with (kF cx fpos + (0x1130 + (x - kW2 cx fpos))) at 1 by lia.
    rewrite (km_div8 (kF cx fpos)) by exact HF8.
    replace (0x1130 + (x - kW2 cx fpos)) with (0x226 * 8 + (x - kW2 cx fpos)) by lia.
    rewrite Z.div_add_l by lia. lia. }
  eapply SRr_bind.
  - eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet 0x53214 AMEMSET (k_G cx) (k_XO cx) (k_OUT cx) W3 rg
      (ms_mem ms3) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) _ ly3 S3 md3 k2
      (kW2 cx fpos) 0 NW_SIZE raw HGok HJ R10 R11 R12);
    [ unfold NW_SIZE; lia | unfold kW2, KN_W2; lia | unfold kW2, KN_W2, NW_SIZE; lia
    | rewrite Hsp; lia | rewrite Hsp, HES; rewrite HK8 in S6; lia | rewrite Hsp; lia
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | exact R1 | exact Hraw
    | | | | | exact I ].
    + intros a Ha. left. split; [|split].
      * right. right. right. exists KN_CID, fpos. split; [left; reflexivity|]. left.
        unfold in_zr. cbn [fst snd]. rewrite (km_fa cx fpos k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ), kn_fsb8.
        fold (kF cx fpos). unfold kW2, KN_W2, NW_SIZE in Ha. lia.
      * unfold kW2, KN_W2, NW_SIZE in Ha. lia.
      * rewrite Hsp, HES. rewrite HK8 in S6. unfold kW2, KN_W2, NW_SIZE in Ha. lia.
    + unfold amem_range, kLowMemEnd, kHighMemEnd, kW2, KN_W2, NW_SIZE. unfold kHighMemBeg in *. lia.
    + intros x Hx. exists 0. split; [|left; reflexivity].
      rewrite (Hsh8 x Hx).
      assert (Hi : 0x226 <= 0x226 + (x - kW2 cx fpos) / 8 < 0x428).
      { unfold NW_SIZE in Hx. split; [pose proof (Z.div_pos (x - kW2 cx fpos) 8); lia|].
        assert ((x - kW2 cx fpos) / 8 < 514) by (apply Z.div_lt_upper_bound; lia). lia. }
      rewrite (km_sh_at cx fpos W3 ms3 _ _ HSH) by (rewrite kfsh_length; lia).
      rewrite kfsh_w2z by exact Hi. reflexivity.
    + intros _ s Hs.
      assert (E1 : shadow_addr (kW2 cx fpos) = kFSH cx fpos + 0x226).
      { pose proof (Hsh8 (kW2 cx fpos) ltac:(unfold NW_SIZE; lia)) as Hq.
        unfold shadow_of_addr in Hq. unfold shadow_addr. rewrite Hq. rewrite Z.sub_diag. reflexivity. }
      assert (E2 : shadow_addr (kW2 cx fpos + NW_SIZE - 1) = kFSH cx fpos + 0x427).
      { pose proof (Hsh8 (kW2 cx fpos + NW_SIZE - 1) ltac:(unfold NW_SIZE; lia)) as Hq.
        unfold shadow_of_addr in Hq. unfold shadow_addr. rewrite Hq. f_equal.
        replace (kW2 cx fpos + NW_SIZE - 1 - kW2 cx fpos) with 4111 by (unfold NW_SIZE; lia). reflexivity. }
      rewrite E1, E2 in Hs.
      assert (Hlo : kFSH cx fpos + 0x220 <= s < kFSH cx fpos + 0x428).
      { assert (D1 : (kFSH cx fpos + 0x226) / 8 * 8 = kFSH cx fpos + 0x220) by lia.
        assert (D2 : (kFSH cx fpos + 0x427) / 8 * 8 = kFSH cx fpos + 0x420) by lia.
        lia. }
      replace s with (kFSH cx fpos + (s - kFSH cx fpos)) by lia.
      rewrite (km_sh_at cx fpos W3 ms3 _ _ HSH) by (rewrite kfsh_length; lia). discriminate.
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Hfr & Hpres & Hsbm).
    apply (CONT regs2 mem2 md2 HJ2 HP2); [| | exact Hpres | exact Hsbm].
    + intros i Hi. rewrite (Hset i Hi). reflexivity.
    + intros a Ha Hd Hw. apply Hfr; [exact Ha | exact Hd | rewrite Hsp; exact Hw].
Qed.

(* ---- a cut's machine state, its register sub-lists ---- *)
Lemma km_ms_shape : forall (ms : machine_state) (pc : Z),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (w64 pc) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc mm rm] pc H1 H2 H3 H4 H5 H6.
  cbn in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

Lemma km_kat_rl : forall cx fpos pc rl rl' sl sh live adv g k2 ly3 S3 W3 ms3 md3,
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 -> (forall x, In x rl' -> In x rl) ->
  kat B cx fpos pc rl' sl sh live adv g k2 ly3 S3 W3 ms3 md3.
Proof.
  intros cx fpos pc rl rl' sl sh live adv g k2 ly3 S3 W3 ms3 md3
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hs.
  refine (conj H1 (conj H2 (conj _ (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10
    (conj H11 H12))))))))))).
  unfold kregs_eq in *. rewrite Forall_forall in *. intros x Hx. exact (H3 x (Hs x Hx)).
Qed.

(* the shadow address expression of atom nn + c *)
Lemma km_denot_sh : forall E nn v c, ew E nn = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
  ew E 20%nat = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E (km_sh nn c) = Z_to_bv 64 (SHADOW_OFF + (v + c) / 8).
Proof.
  intros E nn v c Hn Hv Hc Hvc H20. unfold km_sh. rewrite denot_lit_U. f_equal.
  assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E nn v c Hn ltac:(lia) ltac:(lia)).
  rewrite (U_atom_off E 20 SHADOW_OFF 0 H20 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite Z.add_0_r. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* F's shadow lies in the shadow band, far below the stack *)
Lemma km_FSH_bound : forall cx fpos k2 ly3 S3 md3, kjbk B cx fpos k2 ly3 S3 md3 ->
  SHADOW_OFF + 512 <= kFSH cx fpos /\ kFSH cx fpos + 2048 <= kHighMemBeg.
Proof.
  intros cx fpos k2 ly3 S3 md3 HJB.
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  pose proof asan_consts as ((C1a & C1b) & _). rewrite kn_fsb8 in F2.
  assert (Hf8 : kF cx fpos / 8 <= 2 ^ 44 - 2048) by (apply Z.div_le_upper_bound; lia).
  assert (Hf0 : 512 <= kF cx fpos / 8) by (apply Z.div_le_lower_bound; lia).
  unfold kFSH, shadow_of_addr, kHighMemBeg, SHADOW_OFF. lia.
Qed.

(* ---- this lane's own cuts (between kin_msg0 / kin_mz and kin_loop / kin_qmsg) ---- *)

(* the message path's registers after +0x5a4: s5 = w2, s6 = ci, s8, s9 = &w2.n, s3 = the cursor's n *)
Definition kregs_m5 (cx : kcx) (fpos ci n : Z) : list (nat * Z) :=
  [(21%nat, kW2 cx fpos); (22%nat, ci); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (19%nat, n)].

(* +0x5b4: meta_fill_00 on w2's shadow returned; slot KS_CI written (+0x5a0), s3 := the cursor's n (+0x5a4) *)
Definition kin_m5b4 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat B cx fpos 0x5b4 (kregs_m5 cx fpos ci (k_wn cx - adv))
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)]) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.

(* +0x5c4: checked_memset(w2, 0, 4112) returned: w2's fields are 0 *)
Definition kin_m5c4 (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kw_at W3 ms3 (kW2 cx fpos) 0 0 /\
  kat B cx fpos 0x5c4 (kregs_m5 cx fpos ci (k_wn cx - adv))
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci)]) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.

(* +0x1e8c: the empty cursor's meta_fill_00 on w2's shadow returned; slot KS_CI written (+0x1e7c) *)
Definition kin_z1e8c (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat B cx fpos 0x1e8c (kregs_chunk cx fpos ci) (kslots_setup cx fpos c ++ [(KS_CI, ci)]) (kfsh 0xf8 0 0xf3) true
    (k_wn cx) (Some j) k2 ly3 S3 W3 ms3 md3.

End b.
End a.
