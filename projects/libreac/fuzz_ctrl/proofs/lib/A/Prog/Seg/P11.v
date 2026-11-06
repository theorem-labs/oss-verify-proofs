(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 232 of its 267 lines of code are new or changed and 361 lines of the source are left out. *)
(* Segment P11 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): 0x81c60-0x81c80, 9 instructions
   (v1.8 0x81bdc-0x81bf4, 7 instructions; S_P11 is CHANGED: each v1.8 `bne`/`bnez` to the error block became a
   `beq`/`beqz` over a `j` to it, branch relaxation after the function grew).
     81c60 li a1,-1; 81c64 beq a0,a1,81c6c (taken: a0 = -1, the ports_unknown result; NEW-only);
     81c68 j 82bf4 (NEW-only, not reached);
     81c6c ld a0,280(s1) (a0 = code = fr + 3040, the spill XC carries); 81c70 lbu a0,0(a0) (the code byte, 0 since
     P10's callee cleared it; this load has no instrumented check); 81c74 beqz a0,81c7c (taken; NEW-only);
     81c78 j 82bf4 (NEW-only, not reached); 81c7c li a0,14; 81c80 jal reac_ctrl_kind_name@0x8351c.
   (v1.8 -> v1.9 pcs: 81bdc -> 81c60, 81be0 `bne` -> 81c64 / 81c68, 81be4 -> 81c6c, 81be8 -> 81c70, 81bec `bnez`
   -> 81c74 / 81c78, 81bf0 -> 81c7c, 81bf4 -> 81c80; the error block 82b34 -> 82bf4.)
   With x = 14 > 13 the callee returns QMARK = 0x211e0 (the "?" string, v1.8 0x211c0) and writes only its 16-byte
   stack window [sp - 16, sp), so FRA, XC and our[] move across the call with P7's stk_call. The callee premises
   come from the entry cut: the kind-name table at KIND_NAME = 0x9e760 (v1.8 0x9e6a0) lies in the GNU_RELRO range
   (v1.9 0x9e348 .. 0xa1000), so its bytes are the image's (FRA's G_img_c; membership in FrameAPI.frame_RELRO is
   decided by computation, whatever the list's shape), and it lies in a registered global of frame_AG, so its 112
   bytes are addressable (FRA's frame_AG clause); the strings are
   read-only image bytes (FRA's ro_agree); the runtime cells and the shadow map from RT; the sp-anchored window from
   fra_sp.
   Both cuts are SlotInv's: the entry Inv_A81c60 and the exit Inv_A81c84 (the frozen body, a0 = QMARK, the
   kind-name strings, QMARK's two bytes addressable (frame_AG (0x211e0, 2)), XC and the gap-4 facts CUR, IDBe, FGBe
   of aslot push 11); P12 reads the string at a0 through the instrumented checks at 0x81c84-0x81cb8. CUR, IDBe and
   FGBe move across the call with stk_call (the run keeps s6 / s9), as do push 12's spill [s1 + 144] = fr + 2688
   and the 17 addressable bytes at fr + 2691 and push 13's PRO (v1.9: 16 conjuncts, the last [A + 32] = fr + 2880;
   P11 writes no spill). The fragment-record spill is [s1 + 192] in v1.9 (v1.8 [s1 + 208]).
   v1.9 re-fit BUILT on v1.9 facts: rc=0 on a build machine workspace (internal path) (a copy of (internal path) at a working branch e3c0b7a9d6,
   FACTS ed6b6b7b0ab) with the cut base a working branch cf5ad0d7203, 2026-10-28. The callee constants are
   the relocated ones (a working branch 3eade53eef2: REAC_CTRL_KIND_NAME 0x8351c, KIND_NAME 0x9e760,
   QMARK 0x211e0). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot P7.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- the callee's memory premises, from the image ---- *)

(* The image holds the kind-name table at KIND_NAME: a byte-by-byte check, computed. *)
Definition p11_chk_at (i : nat) : bool :=
  match seg_rom rsegs (wa (KIND_NAME + Z.of_nat i)), nth_error kind_name_bytes i with
  | Some b, Some b' => bv_eqb b b'
  | _, _ => false
  end.

(* p11_chk computes on Img0's bytes at KIND_NAME (0x9e760 in v1.9). *)
Lemma p11_chk : forallb p11_chk_at (seq 0 112) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p11_kn_rom : forall i, (i < 112)%nat ->
  seg_rom rsegs (wa (KIND_NAME + Z.of_nat i)) = nth_error kind_name_bytes i.
Proof.
  intros i Hi.
  pose proof (proj1 (forallb_forall p11_chk_at (seq 0 112)) p11_chk i (proj2 (in_seq 112 0 i) ltac:(lia))) as H.
  unfold p11_chk_at in H. revert H.
  destruct (seg_rom rsegs (wa (KIND_NAME + Z.of_nat i))) as [b|]; [|intros H; discriminate H].
  destruct (nth_error kind_name_bytes i) as [b'|]; [|intros H; discriminate H].
  intros H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. subst b'. reflexivity.
Qed.

(* Membership in a global-range list (FrameAPI's frame_RELRO / frame_AG), decided byte by byte by computation, so
   that no proof here depends on how many ranges the list has or in which order (v1.9 frame batch 2 made
   frame_RELRO one range; v1.8 had three). *)
Definition p11_in_b (G : list (Z * Z)) (a : Z) : bool :=
  existsb (fun e => (fst e <=? a) && (a <? fst e + snd e)) G.

Lemma p11_in_b_ok : forall G a, p11_in_b G a = true -> in_globals G a.
Proof.
  intros G a H. unfold p11_in_b in H. apply existsb_exists in H. destruct H as ((lo & len) & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  hnf. exists lo, len. split; [exact Hin | lia].
Qed.

Lemma p11_in_range : forall G p (n : nat), forallb (fun i => p11_in_b G (p + Z.of_nat i)) (seq 0 n) = true ->
  forall a, p <= a < p + Z.of_nat n -> in_globals G a.
Proof.
  intros G p n H a Ha. apply p11_in_b_ok.
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - p)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (p + (a - p)) with a in H by lia. exact H.
Qed.

(* The table lies in the RELRO range (v1.9 KIND_NAME = 0x9e760 in .data.rel.ro 0x9e380 ..; v1.8 0x9e6a0); where
   memory agrees with the image there, the table is in memory. *)
Lemma p11_table : forall m,
  (forall a, in_globals AF.frame_RELRO a -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
  bytes_at rsegs m KIND_NAME kind_name_bytes.
Proof.
  intros m HG.
  assert (HL : length kind_name_bytes = 112%nat) by reflexivity.
  split; [unfold KIND_NAME; lia|].
  split; [rewrite HL; change (Z.of_nat 112) with 112; unfold KIND_NAME; lia|].
  intros i Hi. rewrite HL in Hi.
  rewrite (HG (KIND_NAME + Z.of_nat i)).
  - exact (p11_kn_rom i Hi).
  - (* v1.9 FrameAPI (frame batch 2): frame_RELRO is the one GNU_RELRO range from 0x9e348; the table
       [0x9e760, 0x9e7d0) is inside it. The check is by computation, so it holds for any shape of the list. *)
    apply (p11_in_range AF.frame_RELRO KIND_NAME 112); [vm_compute; reflexivity | lia].
Qed.

(* The kind-name strings are read-only image bytes (reac_ctrl_kind_name.v's strings lemma). From ro_agree: the goal
   moves to the normalized memory (bytes_at crosses mem_rel), where mem_inv holds and rc_ro_in_image applies. *)
Lemma p11_strings : forall m, ro_agree rsegs m -> kind_name_strings m.
Proof.
  intros m Hm x Hx.
  apply (proj2 (bytes_at_rel rsegs m (normalize rsegs m) _ _ (mem_rel_normalize rsegs m Hm))).
  pose proof (mem_inv_normalize rsegs m) as Hmi.
  destruct (Z.leb_spec x 13) as [Hle|Hgt].
  - destruct (rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
      (apply rc_ro_in_image; [exact Hmi | vm_compute; reflexivity]).
  - assert (Ea : kind_name_addr x = QMARK).
    { unfold kind_name_addr. rewrite (proj2 (Z.leb_gt x 13) Hgt). reflexivity. }
    rewrite Ea, (kind_name_big x Hgt).
    apply rc_ro_in_image; [exact Hmi | vm_compute; reflexivity].
Qed.

(* A range of registered-global bytes is addressable (FRA's frame_AG clause, byte by byte). *)
Lemma p11_ag : forall m p n,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall a, p <= a < p + n -> in_globals AF.frame_AG a) ->
  addressable m p n.
Proof.
  intros m p n HAG Hp Hn Hpn Hin. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hpn|].
  intros i Hi. destruct (HAG (p + i) (Hin (p + i) ltac:(lia))) as (_ & _ & _ & H).
  specialize (H 0 ltac:(lia)). rewrite Z.add_0_r in H. exact H.
Qed.

(* v1.9 FrameAPI: frame_AG registers (0x9e760, 112) for the table and (0x211e0, 2) for "?" (v1.8 (0x9e6a0, 112) /
   (0x211c0, 2)). The checks below are by computation, so they hold for any list that covers the two ranges. *)
Lemma p11_ag_table : forall m,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) -> addressable m KIND_NAME 112.
Proof.
  intros m HAG. apply (p11_ag m KIND_NAME 112 HAG); [unfold KIND_NAME; lia | lia | unfold KIND_NAME, APPMEM_END; lia |].
  intros a Ha. apply (p11_in_range AF.frame_AG KIND_NAME 112); [vm_compute; reflexivity |].
  change (Z.of_nat 112) with 112. exact Ha.
Qed.

Lemma p11_ag_qmark : forall m,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) -> addressable m QMARK 2.
Proof.
  intros m HAG. apply (p11_ag m QMARK 2 HAG); [unfold QMARK; lia | lia | unfold QMARK, APPMEM_END; lia |].
  intros a Ha. apply (p11_in_range AF.frame_AG QMARK 2); [vm_compute; reflexivity |].
  change (Z.of_nat 2) with 2. exact Ha.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract, a Section Hypothesis (it is proved in reac_ctrl_kind_name.v; that proof is not imported). *)
Hypothesis HKN : reac_ctrl_kind_name_contract.

Lemma p11_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c lo : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> 0 <= c < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 c)) ->
    bytes_at rsegs m c [Z_to_bv 8 0] ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m ->
    addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    LE.evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c84) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QMARK)
                       a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c84) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c lo -> -> Hc H280 Hcb HT HS HST Hlo Hkt HAC HSW HAD Hout.
  assert (HL280 : ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 c))).
  { pose proof (bytes_at_ov_read rsegs m (A + 280) (le8 (Z_to_bv 64 c)) 0 8 H280
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HLc : ov_read_bytes rsegs m (wa c) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs m c [Z_to_bv 8 0] 0 1 Hcb ltac:(cbn; lia)) as HH.
    cbn [Z.of_nat firstn skipn] in HH. rewrite Z.add_0_r in HH. exact HH. }
  (* v1.9: two taken branches where v1.8 had two not-taken ones (81c64 `beq a0,a1` with a0 = a1 = -1, 81c74
     `beqz a0` with a0 = 0); the NEW-only `j 82bf4` at 81c68 / 81c78 are not reached. *)
  step. (* 81c60 li a1,-1 *)
  step. (* 81c64 beq a0,a1,81c6c (NEW-only) *)
  if_true.
  step. (* 81c6c ld a0,280(s1) *)
  step. (* 81c70 lbu a0,0(a0) *)
  step. (* 81c74 beqz a0,81c7c (NEW-only) *)
  if_true.
  step. (* 81c7c li a0,14 *)
  step. (* 81c80 jal reac_ctrl_kind_name *)
  pose proof HKN as HP. unfold reac_ctrl_kind_name_contract, REAC_CTRL_KIND_NAME in HP.
  eapply evt_cut.
  { eapply HP with (lo := lo).
    all: assumption. }
  intros ms' (a1' & a2' & m' & E & MU & WM & MIi & ST' & _).
  subst ms'.
  match goal with |- context [kind_name_addr (bv_unsigned ?w)] =>
    replace (kind_name_addr (bv_unsigned w)) with QMARK by (vm_compute; reflexivity) end.
  replace (ret_pc (Z_to_bv 64 0x81c84)) with (Z_to_bv 64 0x81c84)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  exists a1', a2', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

Lemma seg_P11 : Hcut B APIf ra (Inv_A81c84 B APIf ra) -> Hcut B APIf ra (Inv_A81c60 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & HOUR & HCUR & HPRO & HSP & HADR & HSP192 & HADF &
    HADI & HIDB & HFGB &
    Ha0 &
    Hcode & HXC & HAD2880).
  subst c. rewrite SEGS.
  pose proof HXC as (HAblk & Hadc).
  pose proof HFRA as (A1 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm2 & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAd & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof HRT as (HAC0 & HSW0 & _).
  destruct (fra_A B APIf ra g fr [] regs mem md HFRA) as (A & HA9 & HAr & HspA & HfrA & HA416').
  destruct (fra_sp B APIf ra g fr [] regs mem md HFRA) as (Hspb & Hspm & HaspB & Hhi & Hwinsp).
  pose proof (HAblk A HA9 HAr) as H280.
  unfold AC.aspZ in Hspb, Hspm, HaspB, Hhi, Hwinsp.
  pose proof (bytes_at_bound rsegs mem (fr + 3040) [Z_to_bv 8 0] Hcode) as Hcr.
  cbn [length] in Hcr.
  assert (HT : bytes_at rsegs mem KIND_NAME kind_name_bytes).
  { apply p11_table. intros a Hin. pose proof (Hgimg a Hin) as H. rewrite SEGS in H. exact H. }
  assert (HAD : addressable mem KIND_NAME 112) by exact (p11_ag_table mem HAG).
  assert (Hout : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
    outside [(bv_unsigned (getr regs 2) - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned (getr regs 2))] x).
  { intros x Hx. cbn [outside]. split; [|exact I].
    intros [H1 H2].
    destruct Hx as [Hx|[Hx|Hx]];
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
        REAC_CTRL_KIND_NAME_FRAME, FN_STACK, AF.SLOT_STACK in *; lia. }
  apply (p7_run regs (Z_to_bv 64 0x81c60) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81c84 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 QMARK /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       munch [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] mem mem' /\
       wmono rsegs mem mem' /\
       stk rsegs mem' (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply p11_evt with (sp := getr regs 2) (A := A) (c := fr + 3040)
        (lo := bv_unsigned (getr regs 2) - REAC_CTRL_KIND_NAME_FRAME).
      - unfold rg in HA9. exact HA9.
      - unfold a0v, rg in Ha0. exact Ha0.
      - lia.
      - unfold q64 in H280. exact H280.
      - unfold b8 in Hcode. exact Hcode.
      - exact HT.
      - exact (p11_strings mem Hro).
      - apply (p7_stk_sub mem (bv_unsigned (getr regs 2) - FN_STACK)); [exact Hwinsp|].
        unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_KIND_NAME_FRAME. lia.
      - lia.
      - unfold KIND_NAME, REAC_CTRL_KIND_NAME_FRAME, FN_STACK, AF.SLOT_STACK, HIGHMEM_BEG in *. lia.
      - exact HAC0.
      - exact HSW0.
      - exact HAD.
      - exact Hout. }
    { intros ms' (a1' & a2' & m' & E & MU & WM & ST').
      eexists _, (Z_to_bv 64 0x81c84), m'. split; [exact E|].
      split; [reflexivity|].
      do 8 (split; [reflexivity|]).
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM | exact ST']. }
  - intros R pc' mem' regs' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K10 & K22 & K25 & MU & WM & ST')
      Hreg Hmat.
    subst pc'.
    (* P7's stk_call (a Theorem Labs lane's v1.9 P7): it takes and returns `spill regs mem 192 (fragb fr)` (v1.8 208). *)
    destruct (stk_call B APIf ra empty FF g fr [] regs regs' mem mem' md md' REAC_CTRL_KIND_NAME_FRAME _ HFRA HENT
      HXC HOUR HCUR HPRO HSP HADR HSP192 HADF HADI HIDB HFGB
      ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_KIND_NAME_FRAME; lia)
      MU WM ST'
      ltac:(rewrite Hreg; exact K2) ltac:(rewrite Hreg; exact K3) ltac:(rewrite Hreg; exact K4)
      ltac:(rewrite Hreg; exact K8) ltac:(rewrite Hreg; exact K9) ltac:(rewrite Hreg; exact K19)
      ltac:(rewrite Hreg; exact K26) ltac:(rewrite Hreg; exact K22) ltac:(rewrite Hreg; exact K25) Hmat)
      as (HFRA' & HENT' & HXC' & HOUR' & HCUR' & HPRO' & HSP' & HADR' & HSP192' & HADF' & HADI' & HIDB' & HFGB').
    pose proof HFRA' as (A2 & sp2 & s52 & HRT2 & HAH2 & Hro2 & Hsn2 & Hhalt2 & Hgimg2 & Hr22 & Hspm22 & Haspz2 &
      Hstklo2 & Hr42 & Hr82 & Hr92 & Hr32 & Hr192 & Hr262 & Hfrm2 & Hs52 & HAm2 & HAS2 & Hspa2 & Hfa2 & HA4162 &
      HS42 & HAPP2 & Hspill2 & Hsel2 & Hfr242 & Hloc2 & Hhdr12 & Hhdr22 & Hsh2 & Hwin2 & Hsaved2 & Herrno2 & HAG2 &
      HWAd2 & HSHI12 & HSHI22 & HSHI32 & Hhb2 & Hlive2).
    (* cut bundle round 4: first.sroa.7's 35 bytes stay addressable (the callee writes only its stack window, which
       is application memory, so no shadow byte changes) *)
    assert (HAD2880' : addressable mem' (fr + 2880) 35).
    { apply (sl_addr_keep mem mem' [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] (fr + 2880) 35
               HAD2880 MU).
      cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. unfold AC.aspZ in Ha.
      unfold REAC_CTRL_KIND_NAME_FRAME, FN_STACK, AF.SLOT_STACK, HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (HIexit : Inv_A81c84 B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 0x81c84) mem' (seg_rom rsegs)) md')).
    { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hn|]. split; [exact HOUR'|].
      split; [unfold a0v, rg; rewrite Hreg; exact K10|].
      split; [exact (p11_strings mem' Hro2)|].
      split; [exact (p11_ag_qmark mem' HAG2)|]. split; [exact HXC'|].
      split; [exact HCUR'|]. split; [exact HPRO'|]. split; [exact HSP'|]. split; [exact HADR'|].
      split; [exact HSP192'|]. split; [exact HADF'|]. split; [exact HADI'|].
      split; [exact HIDB'|]. split; [exact HFGB' | exact HAD2880']. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
