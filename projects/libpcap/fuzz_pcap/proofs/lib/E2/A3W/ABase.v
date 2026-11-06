(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMALLOC_SYM : Z := 0x56178.    (* [comment removed for export] *)
Definition AFREE_SYM : Z := 0x56174.      (* [comment removed for export] *)
Definition AMALLOC_PC : Z := 0x5641c.     (* [comment removed for export] *)
Definition AFREE_PC : Z := 0x562bc.       (* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 4096.     (* [comment removed for export] *)
Definition AFREE_STACK : Z := 4096.
(* [comment removed for export] *)
Class atlsT {rc : runConstT} : Type := ATls {
  ATPv : Z;
  (* [comment removed for export] *)
  kt_img : Z;  kt_sh : Z;  kt_res : Z;  kt_t : Z;
  AAHMv : Z;      (* [comment removed for export] *)
  ATPv_pg : (ATPv - 200) mod 16 = 0;
  ATPv_lo : 4096 + 200 <= ATPv;
  ATPv_hi : ATPv + 3896 <= ATOP;       (* [comment removed for export] *)
  kt_rng : (0 <= kt_img <= 1 /\ 0 <= kt_sh <= 1) /\ (0 <= kt_res <= 1 /\ 0 <= kt_t <= 1);
  ATPv_imgk : ATPv = 0x5e15b8 /\ kt_img = 0;     (* tp = builtin_tls 0x5e14f0 + 200, inside the image's .bss *)
  ATPv_shk : ATPv + 3896 <= 0x7fff7000 + kt_sh * 18446744073709551616 /\ 17594333495496 * kt_sh <= ATPv }.   (* [comment removed for export] *)
Lemma ATPv_img `{atlsT} : ATPv = 0x5e15b8.
Proof. exact (proj1 ATPv_imgk). Qed.
Lemma ATPv_sh `{atlsT} : ATPv + 3896 <= 0x7fff7000 \/ 0x10007fff8000 + 200 <= ATPv.
Proof. pose proof kt_rng as ((_ & K) & _). pose proof ATPv_shk as (A & B). assert (E : kt_sh = 0 \/ kt_sh = 1) by lia. destruct E as [E|E]; rewrite E in *; [left | right]; lia. Qed.
Lemma atp_range `{atlsT} : (ATPv - 200) mod 16 = 0 /\ 4296 <= ATPv /\ ATPv + 3896 <= ATOP /\ ATPv = 0x5e15b8.
Proof. pose proof ATPv_pg; pose proof ATPv_lo; pose proof ATPv_hi; pose proof ATPv_img; auto. Qed.
(* [comment removed for export] *)
Lemma atp_lin `{atlsT} :
  (4296 <= ATPv <= ATOP - 3896 /\ (0 <= kt_img <= 1 /\ 0 <= kt_sh <= 1) /\ (0 <= kt_res <= 1 /\ 0 <= kt_t <= 1))
  /\ (ATPv = 0x5e15b8 /\ kt_img = 0)
  /\ (ATPv + 3896 <= 0x7fff7000 + kt_sh * 18446744073709551616 /\ 17594333495496 * kt_sh <= ATPv).
Proof.
  pose proof ATPv_lo as L; pose proof ATPv_hi as Hh. pose proof kt_rng as (K1 & K2).
  split; [split; [split; [exact L | apply Z.le_add_le_sub_r; exact Hh] | split; [exact K1 | exact K2]] | split; [exact ATPv_imgk | exact ATPv_shk]].
Qed.
(* [comment removed for export] *)
Definition tlsfarb `{atlsT} (k a n : Z) : bool :=
  (a + n <=? ATPv + -200 + k * 18446744073709551616) && (ATPv + 312 <=? a + (1 - k) * 18446744073709551616).
Lemma tlsfarb_true `{atlsT} : forall k a n, tlsfarb k a n = true ->
  a + n <= ATPv + -200 + k * 18446744073709551616 /\ ATPv + 312 <= a + (1 - k) * 18446744073709551616.
Proof. intros k a n E. unfold tlsfarb in E. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. split; assumption. Qed.
Lemma tlsfarb_intro `{atlsT} : forall k a n,
  a + n <= ATPv + -200 + k * 18446744073709551616 -> ATPv + 312 <= a + (1 - k) * 18446744073709551616 -> tlsfarb k a n = true.
Proof. intros k a n E1 E2. unfold tlsfarb. apply andb_true_intro. split; apply Z.leb_le; assumption. Qed.
Ltac tlsfar_expose :=
  repeat match goal with
  | H : _ /\ @tlsfarb ?R ?I ?k ?a ?n = true |- _ =>
      lazymatch goal with
      | _ : a + n <= @ATPv R I + -200 + k * 18446744073709551616 /\ _ |- _ => fail
      | _ => pose proof (@tlsfarb_true R I k a n (proj2 H))
      end
  | H : @tlsfarb ?R ?I ?k ?a ?n = true |- _ =>
      lazymatch goal with
      | _ : a + n <= @ATPv R I + -200 + k * 18446744073709551616 /\ _ |- _ => fail
      | _ => pose proof (@tlsfarb_true R I k a n H)
      end
  end.
Ltac atp_facts :=
  lazymatch goal with
  | |- rng _ _ _ => fail 0 "lia on a footprint goal"      (* [comment removed for export] *)
  | |- _ /\ @tlsfarb _ _ _ _ _ = true => try assumption      (* [comment removed for export] *)
  | _ : (4296 <= @ATPv _ _ <= @ATOP _ - 3896 /\ _) /\ _ |- _ => idtac
  | |- context [@ATPv _ _] => pose proof atp_lin; atop_facts; tlsfar_expose
  | _ => idtac
  end.
Ltac Zify.zify_pre_hook ::= (atop_facts; atp_facts).
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation rng_atls RNG := (rng RNG (ATPv + -200) 504).
Definition ATP `{atlsT} : Z := ATPv.           (* [comment removed for export] *)
Definition AERRNO `{atlsT} : Z := ATPv + -164.       (* [comment removed for export] *)
Definition AREQMAX : Z := 2^29 - 2^16.    (* [comment removed for export] *)
Definition UDEPTH : nat := 28%nat.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x603000.
Definition ARELRO_LO : Z := 0xa4000.
Definition ARELRO_HI : Z := 0xa7000.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KLS : Z := 0x7fff7000.
Definition sclr (a n : Z) : Prop := a + n <= KLS \/ 0x10007fff8000 <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).
Section ABLK. Context {rc : runConstT} {tlsI : atlsT}.
Definition ablk (lo hi : Z) : Prop := (AIMG_HI <= lo /\ hi <= KLS) \/ (0x10007fff8000 <= lo /\ hi <= ATOP).

#[using="Type"] Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= ATOP /\ hi + 8 <= 2^47.
Proof. intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
#[using="Type"] Lemma ablk_img : forall lo hi, ablk lo hi -> AIMG_HI <= lo.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
#[using="Type"] Lemma ablk_top : forall lo hi, ablk lo hi -> hi <= ATOP.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
#[using="Type"] Lemma ablk_kend : forall lo hi, ablk lo hi -> hi + 8 <= KEND.
Proof. intros lo hi H. apply ablk_lin in H. unfold KEND. tauto. Qed.
#[using="Type"] Lemma ablk_sclr : forall lo hi, ablk lo hi -> sclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, sclr in *. lia. Qed.
#[using="Type"] Lemma ablk_iclr : forall lo hi, ablk lo hi -> iclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, iclr, AIMG_HI, AIMG_LO in *. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_app_blk : forall lo hi, ablk lo hi -> lo <= hi -> app_blk lo hi.
Proof. intros lo hi H LE. atop_facts. unfold ablk, app_blk, AIMG_HI, KLS, KLOW, KHIGH, KEND in *. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLS <= a < 0x10007fff8000 -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
#[using="Type"] Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLS \/ 0x10007fff8000 <= lo.
Proof. intros lo hi H. unfold ablk in H. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_shad : forall lo hi, ablk lo hi -> lo <= hi ->
  (shad AIMG_HI <= shad lo /\ shad hi <= shad KLS) \/ (HSH_LO <= shad lo /\ shad hi < HSH_HI).
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_LO, HSH_HI in *.
  Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma ablk_shad_lin : forall lo hi, ablk lo hi -> lo <= hi -> shad AIMG_HI <= shad lo /\ shad hi < HSH_HI.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_HI in *.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_shad_disj : forall lo hi, ablk lo hi -> lo <= hi -> hi <= shad lo \/ shad (hi + 7) + 1 <= lo.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF in *.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Definition wclr (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ sclr (fst iv) (snd iv - fst iv).
#[using="Type"] Lemma wclr_high : forall lo hi, 0x10007fff8000 <= lo -> wclr (lo, hi).
Proof. intros lo hi H. unfold wclr, sclr, AIMG_HI. cbn [fst snd]. lia. Qed.
#[using="Type"] Lemma wclr_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wclr (a, b).
Proof. intros lo hi a b H A B. unfold wclr, sclr, ablk, AIMG_HI, KLS in *. cbn [fst snd]. lia. Qed.
#[using="Type"] Lemma wclr_outside_band : forall W x, Forall wclr W -> KLS <= x < 0x10007fff8000 -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr, sclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
#[using="Type"] Lemma wclr_outside_img : forall W x, Forall wclr W -> x < AIMG_HI -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
#[using="Type"] Lemma wclr_disjoint_band : forall W a n, Forall wclr W -> KLS <= a -> a + n <= 0x10007fff8000 -> disjoint_from W a n.
Proof.
  intros W a n FW H1 H2. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr, sclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
#[using="Type"] Lemma wclr_disjoint_img : forall W a n, Forall wclr W -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  intros W a n FW H. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
(* [comment removed for export] *)
Definition TLS_LO : Z := ATPv + -200.
Definition TLS_LEN : Z := 512.
Definition tclr (a n : Z) : Prop := a + n <= ATPv + -200 \/ ATPv + 312 <= a.
#[using="Type"] Lemma tclr_sub : forall a n a' n', tclr a n -> a <= a' -> a' + n' <= a + n -> tclr a' n'.
Proof. intros a n a' n' H A B. unfold tclr in *. lia. Qed.
#[using="Type"] Lemma atp_sclr : sclr (ATPv + -200) 512.
Proof. pose proof ATPv_sh as S. unfold sclr, KLS. lia. Qed.
#[using="Type"] Lemma atp_iwin : ATPv - 200 = 0x5e14f0 /\ ATPv - 200 + 4096 <= 0x6015c0.
Proof. pose proof ATPv_img as I. lia. Qed.
#[using="Type"] Lemma atp_below_atop : ATPv + 312 <= ATOP.
Proof. pose proof ATPv_hi as Hh. pose proof atop_range as R. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma tclr_int_lem : forall a n, tclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= ATPv + -200 + k * 18446744073709551616 /\ ATPv + 312 <= a + (1 - k) * 18446744073709551616.
Proof. intros a n H G1 G2. pose proof ATPv_lo as L. pose proof ATPv_hi as Hh. unfold tclr in H. destruct H; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma tclr_band : forall a n, KLS <= a -> a + n <= 0x10007fff8000 -> tclr a n.
Proof. intros a n H1 H2. pose proof ATPv_sh as S. unfold tclr, KLS in *. lia. Qed.
#[using="Type"] Lemma tclr_stack : forall a n, ATOP <= a -> tclr a n.
Proof. intros a n H1. pose proof atp_below_atop. unfold tclr. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma shad_in_band : forall a, 0 <= a < 2^47 -> KLS + 4096 <= shad a < 0x10007fff8000.
Proof. intros a H. rewrite shad_div. unfold KLS, ASHOFF. Z.div_mod_to_equations. lia. Qed.
End ABLK.
Ltac tclr_int H :=
  let k := fresh "kt" in let K := fresh "KT" in
  destruct (tclr_int_lem _ _ H ltac:(lia) ltac:(lia)) as (k & K).

(* [comment removed for export] *)
Definition artcells (m : amem) : Prop :=
     rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                                C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6018 [C8 (Z_to_bv 64 0xaf2d9)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae5f8 [C8 (Z_to_bv 64 0x7fff8000)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae600 [C4 (Z_to_bv 64 1)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf2d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf2e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xade5c [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140148 [C8 (Z_to_bv 64 0x1e00010000)]                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1401a0 [C8 (Z_to_bv 64 18446744073709551615)]                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7238 [C8 (Z_to_bv 64 0x9dff0); C8 (Z_to_bv 64 0x9aee0)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa71d8 [C8 (Z_to_bv 64 0x9edb8)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7210 [C8 (Z_to_bv 64 0xa3ea8)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7220 [C8 (Z_to_bv 64 0x9abc8)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7308 [C8 (Z_to_bv 64 0x9eff4)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7200 [C8 (Z_to_bv 64 0x9e5a4)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140178 [C8 (Z_to_bv 64 4294967296)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140220 [C8 (Z_to_bv 64 0x101010101010101)]                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabe58 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x13e098 [C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AINSTANCE : Z := 0xaaf98.     (* [comment removed for export] *)
Definition AFLAGS : Z := 0xabdf8.        (* [comment removed for export] *)
Definition ACFLAGS : Z := 0x140128.       (* [comment removed for export] *)
Definition AINITED : Z := 0xaf2d8.       (* [comment removed for export] *)
Definition ACANPOISON : Z := 0xade5c.    (* [comment removed for export] *)
Definition AMCTXSZ : Z := 0xaf2fc.       (* [comment removed for export] *)
Definition ASHBASE : Z := 0xae5f8.       (* [comment removed for export] *)
Definition AMIDBEG : Z := 0xaf2e8.       (* [comment removed for export] *)
Definition AMIDEND : Z := 0xaf2f0.       (* [comment removed for export] *)
Definition AHIGHEND : Z := 0xaf2e0.      (* [comment removed for export] *)
Definition AREALMEMSET : Z := 0xa7360.   (* [comment removed for export] *)
Definition AMEMSET : Z := 0x9ead4.
Definition APGSZ : Z := 0x13e0a0.         (* [comment removed for export] *)
Definition ATSDI : Z := 0xade60.         (* [comment removed for export] *)
Definition ATSDK : Z := 0xade64.         (* [comment removed for export] *)
Definition ATP88 `{atlsT} : Z := ATPv + -88.         (* [comment removed for export] *)
Definition ATSD : Z := 0x602960.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GOT_PGSZ : Z := 0xa5490.      (* [comment removed for export] *)
Definition GOT_CFLAGS : Z := 0xa54a0.    (* [comment removed for export] *)
Definition GOT_FLAGS : Z := 0xa54a8.     (* [comment removed for export] *)
Definition GOT_SHBASE : Z := 0xa54b0.    (* [comment removed for export] *)
Definition GOT_MIDBEG : Z := 0xa54b8.    (* [comment removed for export] *)
Definition GOT_MIDEND : Z := 0xa54c0.    (* [comment removed for export] *)
Definition GOT_HIGHEND : Z := 0xa54c8.   (* [comment removed for export] *)
Definition GOT_REALMEMSET : Z := 0xa54d0. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Record alayout := mkALayout {
  al_V : nat -> Z;            (* [comment removed for export] *)
  al_w : bool;                (* [comment removed for export] *)
  al_U : list (list Z)        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition al_sp0 (L : alayout) : Z := 32768 * al_V L 0%nat + 16 * al_V L 6%nat.       (* [comment removed for export] *)
Definition al_top (L : alayout) : Z := page_round_up_Z (al_sp0 L - 0xa0).              (* [comment removed for export] *)
Definition al_bot (L : alayout) : Z := al_top L - 0x800000.                             (* [comment removed for export] *)
Definition al_t (L : alayout) : Z := 4096 * al_V L 240%nat.                             (* [comment removed for export] *)
Definition al_ctx (L : alayout) : Z := 4096 * al_V L 241%nat.                           (* [comment removed for export] *)
Definition al_space_beg (L : alayout) : Z := 4096 * (al_V L 221%nat - al_V L 222%nat) + 0x10000.
Definition al_ptr_array (L : alayout) : Z := 4096 * al_V L 239%nat.
Definition al_nodes (L : alayout) : Z := 4096 * al_V L 485%nat.                         (* [comment removed for export] *)
Definition al_store (L : alayout) : Z := 4096 * al_V L 486%nat.                         (* [comment removed for export] *)
Definition al_fake (L : alayout) : Z := 4096 * al_V L 406%nat.                          (* [comment removed for export] *)
Definition AUMAX : Z := 4096.                                                           (* [comment removed for export] *)

Inductive abkind := ABHeap (p : aptr) | ABFake (cls : Z).
Record ablock := mkABlock { ab_kind : abkind; ab_addr : Z; ab_size : Z }.
Notation HB p A n := (mkABlock (ABHeap p) A n).

Definition in_block (LB : list ablock) (a : Z) : Prop :=
  exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b.
Definition in_fake (LB : list ablock) (a : Z) : Prop :=
  exists cls A n, In (mkABlock (ABFake cls) A n) LB /\ A <= a < A + n.

Definition abkind_eqb (k k' : abkind) : bool :=
  match k, k' with
  | ABHeap p, ABHeap p' => (p =? p')%N
  | ABFake c, ABFake c' => c =? c'
  | _, _ => false
  end.
Definition lb_remove (p : aptr) (LB : list ablock) : list ablock :=
  filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap p))) LB.
(* [comment removed for export] *)
Definition hb_ids (LB : list ablock) : list aptr :=
  flat_map (fun b => match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) LB.

(* [comment removed for export] *)
Definition ablock_range {rc : runConstT} (A n : Z) : Prop :=
  ablk A (A + n) /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ablock_shadow (m : amem) (A n : Z) : Prop :=
  forall g, 0 <= g -> 8 * g < n ->
    m (wa (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive uchain (m : amem) (top pc : Z) : Z -> Z -> nat -> list Z -> Prop :=
| uc_stop : forall prev frame k,
    ~ (prev < frame /\ frame < top - 16 /\ frame mod 8 = 0 /\ (0 < k)%nat) ->
    uchain m top pc prev frame k []
| uc_lowpc : forall prev frame k fp ra,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    0 <= ra < 4096 ->
    uchain m top pc prev frame k []
| uc_step : forall prev frame k fp ra tr,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    4096 <= ra < 2^64 -> 0 <= fp < 2^64 ->
    uchain m top pc frame fp (if ra =? pc then k else Nat.pred k) tr ->
    uchain m top pc prev frame k ((if ra =? pc then [] else [ra]) ++ tr).

(* [comment removed for export] *)
Lemma uchain_frame : forall m m' top pc prev frame k tr,
  uchain m top pc prev frame k tr ->
  (forall a, frame - 16 <= a < top -> m' (wa a) = m (wa a)) ->
  uchain m' top pc prev frame k tr.
Proof.
  intros m m' top pc prev frame k tr H. induction H as [prev frame k Hn | prev frame k fp ra H1 H2 H3 H4 B1 B2 Hra | prev frame k fp ra tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH]; intros HM.
  - apply uc_stop. exact Hn.
  - eapply uc_lowpc; eauto.
    + (nd_pre B1 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + (nd_pre B2 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
  - eapply uc_step; eauto.
    + (nd_pre B1 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + (nd_pre B2 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct (Z_lt_le_dec frame fp) as [LT|GE].
      * apply IH. intros a Ha. apply HM. lia.
      * (* [comment removed for export] *)
        inversion HC; subst; [apply uc_stop; assumption | exfalso; lia | exfalso; lia].
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMALLOC_SYM : Z := 0x561e0.    (* [comment removed for export] *)
Definition AFREE_SYM : Z := 0x561dc.      (* [comment removed for export] *)
Definition AMALLOC_PC : Z := 0x56484.     (* [comment removed for export] *)
Definition AFREE_PC : Z := 0x56324.       (* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 4096.     (* [comment removed for export] *)
Definition AFREE_STACK : Z := 4096.
(* [comment removed for export] *)
Class atlsT {rc : runConstT} : Type := ATls {
  ATPv : Z;
  (* [comment removed for export] *)
  kt_img : Z;  kt_sh : Z;  kt_res : Z;  kt_t : Z;
  AAHMv : Z;      (* [comment removed for export] *)
  ATPv_pg : (ATPv - 200) mod 16 = 0;
  ATPv_lo : 4096 + 200 <= ATPv;
  ATPv_hi : ATPv + 3896 <= ATOP;       (* [comment removed for export] *)
  kt_rng : (0 <= kt_img <= 1 /\ 0 <= kt_sh <= 1) /\ (0 <= kt_res <= 1 /\ 0 <= kt_t <= 1);
  ATPv_imgk : ATPv = 0x5e19b8 /\ kt_img = 0;     (* tp = builtin_tls 0x5e18f0 + 200, inside the image's .bss *)
  ATPv_shk : ATPv + 3896 <= 0x7fff7000 + kt_sh * 18446744073709551616 /\ 17594333495496 * kt_sh <= ATPv }.   (* [comment removed for export] *)
Lemma ATPv_img `{atlsT} : ATPv = 0x5e19b8.
Proof. exact (proj1 ATPv_imgk). Qed.
Lemma ATPv_sh `{atlsT} : ATPv + 3896 <= 0x7fff7000 \/ 0x10007fff8000 + 200 <= ATPv.
Proof. pose proof kt_rng as ((_ & K) & _). pose proof ATPv_shk as (A & B). assert (E : kt_sh = 0 \/ kt_sh = 1) by lia. destruct E as [E|E]; rewrite E in *; [left | right]; lia. Qed.
Lemma atp_range `{atlsT} : (ATPv - 200) mod 16 = 0 /\ 4296 <= ATPv /\ ATPv + 3896 <= ATOP /\ ATPv = 0x5e19b8.
Proof. pose proof ATPv_pg; pose proof ATPv_lo; pose proof ATPv_hi; pose proof ATPv_img; auto. Qed.
(* [comment removed for export] *)
Lemma atp_lin `{atlsT} :
  (4296 <= ATPv <= ATOP - 3896 /\ (0 <= kt_img <= 1 /\ 0 <= kt_sh <= 1) /\ (0 <= kt_res <= 1 /\ 0 <= kt_t <= 1))
  /\ (ATPv = 0x5e19b8 /\ kt_img = 0)
  /\ (ATPv + 3896 <= 0x7fff7000 + kt_sh * 18446744073709551616 /\ 17594333495496 * kt_sh <= ATPv).
Proof.
  pose proof ATPv_lo as L; pose proof ATPv_hi as Hh. pose proof kt_rng as (K1 & K2).
  split; [split; [split; [exact L | apply Z.le_add_le_sub_r; exact Hh] | split; [exact K1 | exact K2]] | split; [exact ATPv_imgk | exact ATPv_shk]].
Qed.
(* [comment removed for export] *)
Definition tlsfarb `{atlsT} (k a n : Z) : bool :=
  (a + n <=? ATPv + -200 + k * 18446744073709551616) && (ATPv + 312 <=? a + (1 - k) * 18446744073709551616).
Lemma tlsfarb_true `{atlsT} : forall k a n, tlsfarb k a n = true ->
  a + n <= ATPv + -200 + k * 18446744073709551616 /\ ATPv + 312 <= a + (1 - k) * 18446744073709551616.
Proof. intros k a n E. unfold tlsfarb in E. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. split; assumption. Qed.
Lemma tlsfarb_intro `{atlsT} : forall k a n,
  a + n <= ATPv + -200 + k * 18446744073709551616 -> ATPv + 312 <= a + (1 - k) * 18446744073709551616 -> tlsfarb k a n = true.
Proof. intros k a n E1 E2. unfold tlsfarb. apply andb_true_intro. split; apply Z.leb_le; assumption. Qed.
Ltac tlsfar_expose :=
  repeat match goal with
  | H : _ /\ @tlsfarb ?R ?I ?k ?a ?n = true |- _ =>
      lazymatch goal with
      | _ : a + n <= @ATPv R I + -200 + k * 18446744073709551616 /\ _ |- _ => fail
      | _ => pose proof (@tlsfarb_true R I k a n (proj2 H))
      end
  | H : @tlsfarb ?R ?I ?k ?a ?n = true |- _ =>
      lazymatch goal with
      | _ : a + n <= @ATPv R I + -200 + k * 18446744073709551616 /\ _ |- _ => fail
      | _ => pose proof (@tlsfarb_true R I k a n H)
      end
  end.
Ltac atp_facts :=
  lazymatch goal with
  | |- rng _ _ _ => fail 0 "lia on a footprint goal"      (* [comment removed for export] *)
  | |- _ /\ @tlsfarb _ _ _ _ _ = true => try assumption      (* [comment removed for export] *)
  | _ : (4296 <= @ATPv _ _ <= @ATOP _ - 3896 /\ _) /\ _ |- _ => idtac
  | |- context [@ATPv _ _] => pose proof atp_lin; atop_facts; tlsfar_expose
  | _ => idtac
  end.
Ltac Zify.zify_pre_hook ::= (atop_facts; atp_facts). Ltac twm_hook_1 := (atop_facts; atp_facts).
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation rng_atls RNG := (rng RNG (ATPv + -200) 504).
Definition ATP `{atlsT} : Z := ATPv.           (* [comment removed for export] *)
Definition AERRNO `{atlsT} : Z := ATPv + -164.       (* [comment removed for export] *)
Definition AREQMAX : Z := 2^29 - 2^16.    (* [comment removed for export] *)
Definition UDEPTH : nat := 28%nat.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x604000.
Definition ARELRO_LO : Z := 0xa5000.
Definition ARELRO_HI : Z := 0xa7000.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KLS : Z := 0x7fff7000.
Definition sclr (a n : Z) : Prop := a + n <= KLS \/ 0x10007fff8000 <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).
Section ABLK. Context {rc : runConstT} {tlsI : atlsT}.
Definition ablk (lo hi : Z) : Prop := (AIMG_HI <= lo /\ hi <= KLS) \/ (0x10007fff8000 <= lo /\ hi <= ATOP).

#[using="Type"] Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= ATOP /\ hi + 8 <= 2^47.
Proof. intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
#[using="Type"] Lemma ablk_img : forall lo hi, ablk lo hi -> AIMG_HI <= lo.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
#[using="Type"] Lemma ablk_top : forall lo hi, ablk lo hi -> hi <= ATOP.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
#[using="Type"] Lemma ablk_kend : forall lo hi, ablk lo hi -> hi + 8 <= KEND.
Proof. intros lo hi H. apply ablk_lin in H. unfold KEND. tauto. Qed.
#[using="Type"] Lemma ablk_sclr : forall lo hi, ablk lo hi -> sclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, sclr in *. lia. Qed.
#[using="Type"] Lemma ablk_iclr : forall lo hi, ablk lo hi -> iclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, iclr, AIMG_HI, AIMG_LO in *. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_app_blk : forall lo hi, ablk lo hi -> lo <= hi -> app_blk lo hi.
Proof. intros lo hi H LE. atop_facts. unfold ablk, app_blk, AIMG_HI, KLS, KLOW, KHIGH, KEND in *. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLS <= a < 0x10007fff8000 -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
#[using="Type"] Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLS \/ 0x10007fff8000 <= lo.
Proof. intros lo hi H. unfold ablk in H. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_shad : forall lo hi, ablk lo hi -> lo <= hi ->
  (shad AIMG_HI <= shad lo /\ shad hi <= shad KLS) \/ (HSH_LO <= shad lo /\ shad hi < HSH_HI).
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_LO, HSH_HI in *.
  Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma ablk_shad_lin : forall lo hi, ablk lo hi -> lo <= hi -> shad AIMG_HI <= shad lo /\ shad hi < HSH_HI.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_HI in *.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ablk_shad_disj : forall lo hi, ablk lo hi -> lo <= hi -> hi <= shad lo \/ shad (hi + 7) + 1 <= lo.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF in *.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Definition wclr (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ sclr (fst iv) (snd iv - fst iv).
#[using="Type"] Lemma wclr_high : forall lo hi, 0x10007fff8000 <= lo -> wclr (lo, hi).
Proof. intros lo hi H. unfold wclr, sclr, AIMG_HI. cbn [fst snd]. lia. Qed.
#[using="Type"] Lemma wclr_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wclr (a, b).
Proof. intros lo hi a b H A B. unfold wclr, sclr, ablk, AIMG_HI, KLS in *. cbn [fst snd]. lia. Qed.
#[using="Type"] Lemma wclr_outside_band : forall W x, Forall wclr W -> KLS <= x < 0x10007fff8000 -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr, sclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
#[using="Type"] Lemma wclr_outside_img : forall W x, Forall wclr W -> x < AIMG_HI -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
#[using="Type"] Lemma wclr_disjoint_band : forall W a n, Forall wclr W -> KLS <= a -> a + n <= 0x10007fff8000 -> disjoint_from W a n.
Proof.
  intros W a n FW H1 H2. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr, sclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
#[using="Type"] Lemma wclr_disjoint_img : forall W a n, Forall wclr W -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  intros W a n FW H. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
(* [comment removed for export] *)
Definition TLS_LO : Z := ATPv + -200.
Definition TLS_LEN : Z := 512.
Definition tclr (a n : Z) : Prop := a + n <= ATPv + -200 \/ ATPv + 312 <= a.
#[using="Type"] Lemma tclr_sub : forall a n a' n', tclr a n -> a <= a' -> a' + n' <= a + n -> tclr a' n'.
Proof. intros a n a' n' H A B. unfold tclr in *. lia. Qed.
#[using="Type"] Lemma atp_sclr : sclr (ATPv + -200) 512.
Proof. pose proof ATPv_sh as S. unfold sclr, KLS. lia. Qed.
#[using="Type"] Lemma atp_iwin : ATPv - 200 = 0x5e18f0 /\ ATPv - 200 + 4096 <= 0x6019c0.
Proof. pose proof ATPv_img as I. lia. Qed.
#[using="Type"] Lemma atp_below_atop : ATPv + 312 <= ATOP.
Proof. pose proof ATPv_hi as Hh. pose proof atop_range as R. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma tclr_int_lem : forall a n, tclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= ATPv + -200 + k * 18446744073709551616 /\ ATPv + 312 <= a + (1 - k) * 18446744073709551616.
Proof. intros a n H G1 G2. pose proof ATPv_lo as L. pose proof ATPv_hi as Hh. unfold tclr in H. destruct H; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma tclr_band : forall a n, KLS <= a -> a + n <= 0x10007fff8000 -> tclr a n.
Proof. intros a n H1 H2. pose proof ATPv_sh as S. unfold tclr, KLS in *. lia. Qed.
#[using="Type"] Lemma tclr_stack : forall a n, ATOP <= a -> tclr a n.
Proof. intros a n H1. pose proof atp_below_atop. unfold tclr. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma shad_in_band : forall a, 0 <= a < 2^47 -> KLS + 4096 <= shad a < 0x10007fff8000.
Proof. intros a H. rewrite shad_div. unfold KLS, ASHOFF. Z.div_mod_to_equations. lia. Qed.
End ABLK.
Ltac tclr_int H :=
  let k := fresh "kt" in let K := fresh "KT" in
  destruct (tclr_int_lem _ _ H ltac:(lia) ltac:(lia)) as (k & K).

(* [comment removed for export] *)
Definition artcells (m : amem) : Prop :=
     rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                                C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa63f8 [C8 (Z_to_bv 64 0xaf6d9)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae9f8 [C8 (Z_to_bv 64 0x7fff8000)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaea00 [C4 (Z_to_bv 64 1)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf6d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf6e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae25c [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140548 [C8 (Z_to_bv 64 0x1e00010000)]                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1405a0 [C8 (Z_to_bv 64 18446744073709551615)]                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7618 [C8 (Z_to_bv 64 0x9e3d4); C8 (Z_to_bv 64 0x9b2c4)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa75b8 [C8 (Z_to_bv 64 0x9f19c)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa75f0 [C8 (Z_to_bv 64 0xa428c)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7600 [C8 (Z_to_bv 64 0x9afac)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa76e8 [C8 (Z_to_bv 64 0x9f3d8)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa75e0 [C8 (Z_to_bv 64 0x9e988)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140578 [C8 (Z_to_bv 64 4294967296)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140620 [C8 (Z_to_bv 64 0x101010101010101)]                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac258 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x13e498 [C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AINSTANCE : Z := 0xab398.     (* [comment removed for export] *)
Definition AFLAGS : Z := 0xac1f8.        (* [comment removed for export] *)
Definition ACFLAGS : Z := 0x140528.       (* [comment removed for export] *)
Definition AINITED : Z := 0xaf6d8.       (* [comment removed for export] *)
Definition ACANPOISON : Z := 0xae25c.    (* [comment removed for export] *)
Definition AMCTXSZ : Z := 0xaf6fc.       (* [comment removed for export] *)
Definition ASHBASE : Z := 0xae9f8.       (* [comment removed for export] *)
Definition AMIDBEG : Z := 0xaf6e8.       (* [comment removed for export] *)
Definition AMIDEND : Z := 0xaf6f0.       (* [comment removed for export] *)
Definition AHIGHEND : Z := 0xaf6e0.      (* [comment removed for export] *)
Definition AREALMEMSET : Z := 0xa7740.   (* [comment removed for export] *)
Definition AMEMSET : Z := 0x9eeb8.
Definition APGSZ : Z := 0x13e4a0.         (* [comment removed for export] *)
Definition ATSDI : Z := 0xae260.         (* [comment removed for export] *)
Definition ATSDK : Z := 0xae264.         (* [comment removed for export] *)
Definition ATP88 `{atlsT} : Z := ATPv + -88.         (* [comment removed for export] *)
Definition ATSD : Z := 0x602d60.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GOT_PGSZ : Z := 0xa5870.      (* [comment removed for export] *)
Definition GOT_CFLAGS : Z := 0xa5880.    (* [comment removed for export] *)
Definition GOT_FLAGS : Z := 0xa5888.     (* [comment removed for export] *)
Definition GOT_SHBASE : Z := 0xa5890.    (* [comment removed for export] *)
Definition GOT_MIDBEG : Z := 0xa5898.    (* [comment removed for export] *)
Definition GOT_MIDEND : Z := 0xa58a0.    (* [comment removed for export] *)
Definition GOT_HIGHEND : Z := 0xa58a8.   (* [comment removed for export] *)
Definition GOT_REALMEMSET : Z := 0xa58b0. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Record alayout := mkALayout {
  al_V : nat -> Z;            (* [comment removed for export] *)
  al_w : bool;                (* [comment removed for export] *)
  al_U : list (list Z)        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition al_sp0 (L : alayout) : Z := 32768 * al_V L 0%nat + 16 * al_V L 6%nat.       (* [comment removed for export] *)
Definition al_top (L : alayout) : Z := page_round_up_Z (al_sp0 L - 0xa0).              (* [comment removed for export] *)
Definition al_bot (L : alayout) : Z := al_top L - 0x800000.                             (* [comment removed for export] *)
Definition al_t (L : alayout) : Z := 4096 * al_V L 240%nat.                             (* [comment removed for export] *)
Definition al_ctx (L : alayout) : Z := 4096 * al_V L 241%nat.                           (* [comment removed for export] *)
Definition al_space_beg (L : alayout) : Z := 4096 * (al_V L 221%nat - al_V L 222%nat) + 0x10000.
Definition al_ptr_array (L : alayout) : Z := 4096 * al_V L 239%nat.
Definition al_nodes (L : alayout) : Z := 4096 * al_V L 485%nat.                         (* [comment removed for export] *)
Definition al_store (L : alayout) : Z := 4096 * al_V L 486%nat.                         (* [comment removed for export] *)
Definition al_fake (L : alayout) : Z := 4096 * al_V L 406%nat.                          (* [comment removed for export] *)
Definition AUMAX : Z := 4096.                                                           (* [comment removed for export] *)

Inductive abkind := ABHeap (p : aptr) | ABFake (cls : Z).
Record ablock := mkABlock { ab_kind : abkind; ab_addr : Z; ab_size : Z }.
Notation HB p A n := (mkABlock (ABHeap p) A n).

Definition in_block (LB : list ablock) (a : Z) : Prop :=
  exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b.
Definition in_fake (LB : list ablock) (a : Z) : Prop :=
  exists cls A n, In (mkABlock (ABFake cls) A n) LB /\ A <= a < A + n.

Definition abkind_eqb (k k' : abkind) : bool :=
  match k, k' with
  | ABHeap p, ABHeap p' => (p =? p')%N
  | ABFake c, ABFake c' => c =? c'
  | _, _ => false
  end.
Definition lb_remove (p : aptr) (LB : list ablock) : list ablock :=
  filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap p))) LB.
(* [comment removed for export] *)
Definition hb_ids (LB : list ablock) : list aptr :=
  flat_map (fun b => match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) LB.

(* [comment removed for export] *)
Definition ablock_range {rc : runConstT} (A n : Z) : Prop :=
  ablk A (A + n) /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ablock_shadow (m : amem) (A n : Z) : Prop :=
  forall g, 0 <= g -> 8 * g < n ->
    m (wa (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive uchain (m : amem) (top pc : Z) : Z -> Z -> nat -> list Z -> Prop :=
| uc_stop : forall prev frame k,
    ~ (prev < frame /\ frame < top - 16 /\ frame mod 8 = 0 /\ (0 < k)%nat) ->
    uchain m top pc prev frame k []
| uc_lowpc : forall prev frame k fp ra,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    0 <= ra < 4096 ->
    uchain m top pc prev frame k []
| uc_step : forall prev frame k fp ra tr,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    4096 <= ra < 2^64 -> 0 <= fp < 2^64 ->
    uchain m top pc frame fp (if ra =? pc then k else Nat.pred k) tr ->
    uchain m top pc prev frame k ((if ra =? pc then [] else [ra]) ++ tr).

(* [comment removed for export] *)
Lemma uchain_frame : forall m m' top pc prev frame k tr,
  uchain m top pc prev frame k tr ->
  (forall a, frame - 16 <= a < top -> m' (wa a) = m (wa a)) ->
  uchain m' top pc prev frame k tr.
Proof.
  intros m m' top pc prev frame k tr H. induction H as [prev frame k Hn | prev frame k fp ra H1 H2 H3 H4 B1 B2 Hra | prev frame k fp ra tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH]; intros HM.
  - apply uc_stop. exact Hn.
  - eapply uc_lowpc; eauto.
    + (nd_pre B1 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + (nd_pre B2 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
  - eapply uc_step; eauto.
    + (nd_pre B1 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + (nd_pre B2 3%nat; intros X Y B; nd_post). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct (Z_lt_le_dec frame fp) as [LT|GE].
      * apply IH. intros a Ha. apply HM. lia.
      * (* [comment removed for export] *)
        inversion HC; subst; [apply uc_stop; assumption | exfalso; lia | exfalso; lia].
Qed.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_pre_hook ::= (atop_facts; atp_facts).
