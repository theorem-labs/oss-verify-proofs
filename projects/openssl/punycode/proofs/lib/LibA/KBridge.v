(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require CatSim.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step RegShape.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require FpLift WpEngine LibKit WpTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Run.
Variable segs : list Segment.

Lemma msteps_exec : forall a b, CatSim.msteps segs a b -> Exec.msteps segs a b.
Proof.
  intros a b H. induction H as [ms|ms ms1 ms2 Hsvc Hst _ IH]; [apply msteps_refl|].
  eapply msteps_cons; [split; [exact Hsvc | exact Hst] | exact IH].
Qed.

Lemma mkstF_MS : forall regs F fc pc M rom, FpLift.mkstF regs F fc pc M rom = MS regs F pc fc None M rom.
Proof. reflexivity. Qed.
End Run.
Section Run2.
Variable segs : list Segment.
Import WpEngine.

(* [comment removed for export] *)
Definition lofR (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  : regfile :=
  [Z_to_bv 64 0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25;
   x26; x27; x28; x29; x30; x31].

Lemma rrel_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  rrel (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       (lofR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof.
  intros. split; [reflexivity|]. intros r. destruct (reg_cases r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [reflexivity|]). exfalso; lia.
Qed.
End Run2.
Section Run3.
Variable segs : list Segment.
Import WpEngine.

(* [comment removed for export] *)
Lemma mkR_of_rrel : forall R l, shaped R -> rrel R l ->
  R = mkR (rget l 1) (rget l 2) (rget l 3) (rget l 4) (rget l 5) (rget l 6) (rget l 7) (rget l 8) (rget l 9) (rget l 10)
          (rget l 11) (rget l 12) (rget l 13) (rget l 14) (rget l 15) (rget l 16) (rget l 17) (rget l 18) (rget l 19) (rget l 20)
          (rget l 21) (rget l 22) (rget l 23) (rget l 24) (rget l 25) (rget l 26) (rget l 27) (rget l 28) (rget l 29) (rget l 30)
          (rget l 31).
Proof.
  intros R l (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
              & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->) [HL H].
  assert (HR : rrel (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) l) by (split; assumption).
  rewrite <- (rrel_getr _ _ 1 HR) by lia.
  rewrite <- (rrel_getr _ _ 2 HR) by lia.
  rewrite <- (rrel_getr _ _ 3 HR) by lia.
  rewrite <- (rrel_getr _ _ 4 HR) by lia.
  rewrite <- (rrel_getr _ _ 5 HR) by lia.
  rewrite <- (rrel_getr _ _ 6 HR) by lia.
  rewrite <- (rrel_getr _ _ 7 HR) by lia.
  rewrite <- (rrel_getr _ _ 8 HR) by lia.
  rewrite <- (rrel_getr _ _ 9 HR) by lia.
  rewrite <- (rrel_getr _ _ 10 HR) by lia.
  rewrite <- (rrel_getr _ _ 11 HR) by lia.
  rewrite <- (rrel_getr _ _ 12 HR) by lia.
  rewrite <- (rrel_getr _ _ 13 HR) by lia.
  rewrite <- (rrel_getr _ _ 14 HR) by lia.
  rewrite <- (rrel_getr _ _ 15 HR) by lia.
  rewrite <- (rrel_getr _ _ 16 HR) by lia.
  rewrite <- (rrel_getr _ _ 17 HR) by lia.
  rewrite <- (rrel_getr _ _ 18 HR) by lia.
  rewrite <- (rrel_getr _ _ 19 HR) by lia.
  rewrite <- (rrel_getr _ _ 20 HR) by lia.
  rewrite <- (rrel_getr _ _ 21 HR) by lia.
  rewrite <- (rrel_getr _ _ 22 HR) by lia.
  rewrite <- (rrel_getr _ _ 23 HR) by lia.
  rewrite <- (rrel_getr _ _ 24 HR) by lia.
  rewrite <- (rrel_getr _ _ 25 HR) by lia.
  rewrite <- (rrel_getr _ _ 26 HR) by lia.
  rewrite <- (rrel_getr _ _ 27 HR) by lia.
  rewrite <- (rrel_getr _ _ 28 HR) by lia.
  rewrite <- (rrel_getr _ _ 29 HR) by lia.
  rewrite <- (rrel_getr _ _ 30 HR) by lia.
  rewrite <- (rrel_getr _ _ 31 HR) by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Theorem reach_evt : forall rom pcw M (Post : word -> regfile -> mem -> Prop)
    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc,
  reach segs rom pcw (lofR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                             x28 x29 x30 x31) M Post ->
  evt segs (fun ms' => exists pcw' l' M', length l' = 32%nat /\ Post pcw' l' M' /\
              ms' = MS (mkR (rget l' 1) (rget l' 2) (rget l' 3) (rget l' 4) (rget l' 5) (rget l' 6) (rget l' 7) (rget l' 8)
                            (rget l' 9) (rget l' 10) (rget l' 11) (rget l' 12) (rget l' 13) (rget l' 14) (rget l' 15) (rget l' 16)
                            (rget l' 17) (rget l' 18) (rget l' 19) (rget l' 20) (rget l' 21) (rget l' 22) (rget l' 23) (rget l' 24)
                            (rget l' 25) (rget l' 26) (rget l' 27) (rget l' 28) (rget l' 29) (rget l' 30) (rget l' 31))
                       F pcw' fc None M' rom)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F pcw fc None M rom).
Proof.
  intros. destruct (H _ F fc (rrel_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
                                        x26 x27 x28 x29 x30 x31)) as (pcw' & regs' & l' & M' & Hms & HR & HP).
  apply msteps_exec in Hms. rewrite !mkstF_MS in Hms.
  pose proof (msteps_shaped segs _ _ Hms (shaped_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as SH.
  cbn [ms_regs MS] in SH.
  exists (MS regs' F pcw' fc None M' rom). split; [exact Hms|].
  exists pcw', l', M'. split; [exact (proj1 HR)|]. split; [exact HP|].
  rewrite (mkR_of_rrel regs' l' SH HR) at 1. reflexivity.
Qed.
End Run3.
(* [comment removed for export] *)
Section Run4.
Variable segs : list Segment.

Theorem spec_evt : forall rom pc pc' (M : word -> option byte) (Phi : bvmap 5 word -> (word -> option byte) -> Prop)
    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc,
  (exists regs' M', CatSim.msteps segs
       (FpLift.mkstF (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
                          x29 x30 x31) F fc pc M rom) (FpLift.mkstF regs' F fc pc' M' rom) /\ Phi regs' M') ->
  evt segs (fun ms' => exists y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                              y28 y29 y30 y31 M',
              ms' = MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
                            y29 y30 y31) F pc' fc None M' rom
              /\ Phi (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
                          y29 y30 y31) M')
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F pc fc None M rom).
Proof.
  intros until fc. intros (regs' & M' & Hms & HP).
  apply msteps_exec in Hms. rewrite !mkstF_MS in Hms.
  pose proof (msteps_shaped segs _ _ Hms (shaped_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as SH.
  cbn [ms_regs MS] in SH.
  destruct SH as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                  & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & ->).
  exists (MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             F pc' fc None M' rom).
  split; [exact Hms|].
  exists y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26,
         y27, y28, y29, y30, y31, M'.
  split; [reflexivity | exact HP].
Qed.
End Run4.

Section Voc.
Variable segs : list Segment.
(* [comment removed for export] *)
Variables LO HI : Z.
Hypothesis Hhull : forall a : word, bv_unsigned a < LO \/ HI <= bv_unsigned a -> seg_rom segs a = None.
Hypothesis HLO : 0 <= LO.
Local Abbreviation kcell := (LibKit.cell segs).
Local Abbreviation W z := (Z_to_bv 64 z) (only parsing).

Lemma W_wa : forall a, W a = wa a. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cell_of_bytes : forall (m : word -> option byte) a (n : nat) v,
  bytes_at segs m a (word_to_le_bytes n v) -> kcell m a n v.
Proof.
  intros m a n v H. unfold LibKit.cell.
  pose proof (bytes_at_rdn segs m a _ 0 n H) as R. rewrite Z.add_0_r in R. cbn [skipn] in R.
  unfold word_to_le_bytes in *. rewrite length_Z_to_le_bytes in R. specialize (R ltac:(lia)).
  rewrite <- (length_Z_to_le_bytes n (bv_unsigned v)) in R at 2. rewrite firstn_all in R. exact R.
Qed.

Lemma cell_C8 : forall (m : word -> option byte) a v, ro_cells segs m a [C8 v] -> kcell m a 8 v.
Proof. intros m a v [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. apply cell_of_bytes. exact H. Qed.
Lemma cell_C4 : forall (m : word -> option byte) a v, ro_cells segs m a [C4 v] -> kcell m a 4 v.
Proof. intros m a v [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. apply cell_of_bytes. exact H. Qed.
Lemma cell_C1 : forall (m : word -> option byte) a (b : byte), ro_cells segs m a [C1 b] -> kcell m a 1 (zxb b).
Proof.
  intros m a b [_ H]. cbn [cells_bytes cbytes app] in H. apply cell_of_bytes.
  replace (word_to_le_bytes 1 (zxb b)) with [b]; [exact H|]. symmetry. exact (le1_zxb b).
Qed.

(* [comment removed for export] *)
Lemma mrd_off : forall (m : word -> option byte) (x : Z) b, 0 <= x < 2 ^ 64 -> (x < LO \/ HI <= x) ->
  mrd segs m (wa x) = Some b -> m (W x) = Some b.
Proof.
  intros m x b Hx HO H. unfold mrd in H. rewrite W_wa. destruct (m (wa x)) as [b0|]; [exact H|].
  rewrite Hhull in H by (rewrite wa_unsigned by lia; exact HO). discriminate H.
Qed.

Lemma bytes_off : forall (m : word -> option byte) a bs i, bytes_at segs m a bs ->
  (a + Z.of_nat (length bs) <= LO \/ HI <= a) -> 0 <= i < Z.of_nat (length bs) ->
  m (W (a + i)) = nth_error bs (Z.to_nat i).
Proof.
  intros m a bs i (H0 & H1 & H) HO Hi. pose proof (H (Z.to_nat i) ltac:(lia)) as R. rewrite Z2Nat.id in R by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  apply mrd_off; [lia | lia | exact R].
Qed.

Lemma rd_ok_bytes : forall (m : word -> option byte) a bs, bytes_at segs m a bs ->
  (a + Z.of_nat (length bs) <= LO \/ HI <= a) -> LibKit.rd_ok m a (Z.of_nat (length bs)).
Proof.
  intros m a bs H HO i Hi. rewrite (bytes_off m a bs i H HO Hi).
  destruct (nth_error bs (Z.to_nat i)) eqn:E; [discriminate| apply nth_error_None in E; lia].
Qed.

Lemma rd_ok_stk : forall (m : word -> option byte) lo hi a n, stk segs m lo hi -> (hi <= LO \/ HI <= lo) ->
  lo <= a -> a + n <= hi -> LibKit.rd_ok m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) HO H1 H2 i Hi. destruct (S (a + i) ltac:(lia)) as (_ & b & Hb).
  rewrite (mrd_off m (a + i) b ltac:(lia) ltac:(lia) Hb). discriminate.
Qed.

Lemma wr_ok_wr_at : forall (m : word -> option byte) a n a' n', wr_at segs m a n -> a <= a' -> a' + n' <= a + n ->
  LibKit.wr_ok segs m a' n'.
Proof.
  intros m a n a' n' Hw H1 H2 x j Hx Hj.
  pose proof (wr_at_store_ok segs m a n (x - a) j Hw ltac:(lia) ltac:(lia)) as S.
  replace (a + (x - a)) with x in S by lia. exact S.
Qed.

Lemma wr_ok_stk : forall (m : word -> option byte) lo hi a n, stk segs m lo hi -> lo <= a -> a + n <= hi -> LibKit.wr_ok segs m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) H1 H2. apply (wr_ok_wr_at m lo (hi - lo)); [| lia | lia].
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (lo + i) ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma munch_of_unch : forall (Wl : list ivl) (M M' : word -> option byte) (P : word -> Prop),
  LibKit.unch M M' P -> (forall x : word, P x -> ~ outside Wl (bv_unsigned x)) -> munch Wl M M'.
Proof.
  intros Wl M M' P HU HP x Hx. apply HU. intros HPx. exact (HP x HPx Hx).
Qed.

Lemma wmono_of_grows : forall (M M' : word -> option byte), StoreOk.mem_grows M M' -> wmono segs M M'.
Proof. intros M M' HG x Hx. exact (StoreOk.wview_grows segs M M' x HG Hx). Qed.

Lemma stk_grows : forall (M M' : word -> option byte) lo hi, stk segs M lo hi -> StoreOk.mem_grows M M' -> stk segs M' lo hi.
Proof.
  intros M M' lo hi (S0 & S1 & S) HG. split; [exact S0|]. split; [exact S1|]. intros a Ha.
  destruct (S a Ha) as (Wv & b & Hb). split; [exact (StoreOk.wview_grows segs M M' _ HG Wv)|].
  unfold mrd in *. destruct (M' (wa a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  destruct (M (wa a)) as [b0|] eqn:E0; [exfalso; apply (HG (wa a)); [rewrite E0; discriminate | exact E']|].
  exists b. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma mem_inv_unch : forall (M M' : word -> option byte) (P : word -> Prop), mem_inv segs M -> LibKit.unch M M' P ->
  (forall x : word, P x -> wview segs M x <> None) -> mem_inv segs M'.
Proof.
  intros M M' P MI HU HW. apply mem_inv_intro.
  - intros a Ha. exact (mem_inv_seg_below segs M a MI Ha).
  - intros a b Hb.
    assert (D : M' a = M a \/ wview segs M a <> None).
    { destruct (wview segs M a) eqn:E; [right; discriminate|]. left. apply HU. intros HP. exact (HW a HP E). }
    destruct D as [D|D].
    + rewrite D in Hb. split; [exact (mem_inv_ro segs M a b MI Hb) | exact (mem_inv_ov_below segs M a b MI Hb)].
    + split; [| exact (wview_below segs M a MI D)].
      destruct (M a) as [b0|] eqn:E; [exact (mem_inv_ro segs M a b0 MI E) | exact (wview_not_ro segs M a D E)].
Qed.

(* [comment removed for export] *)
Lemma bytes_of_cell : forall (m : word -> option byte) a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  kcell m a n v -> bytes_at segs m a (word_to_le_bytes n v).
Proof.
  intros m a n v Ha Hn H. unfold LibKit.cell in H. rewrite W_wa in H. revert a Ha Hn H.
  generalize (word_to_le_bytes n v) as bs. induction n as [|n IH]; intros bs a Ha Hn H; rewrite rdn_unfold in H.
  - injection H as <-. apply bytes_at_nil. lia.
  - destruct (mrd segs m (wa a)) as [b|] eqn:E; [| discriminate H]. rewrite wa_succ in H.
    destruct (rdn segs m (wa (a + 1)) n) as [r|] eqn:E2; [| discriminate H]. injection H as <-.
    pose proof (IH r (a + 1) ltac:(lia) ltac:(lia) E2) as (R0 & R1 & R).
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact E.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply R. cbn [length] in Hi. lia.
Qed.
End Voc.

(* [comment removed for export] *)
Lemma notin_b : forall (k : nat) (ks : list nat), forallb (fun j => negb (Nat.eqb j k)) ks = true -> ~ In k ks.
Proof.
  intros k ks H Hin. rewrite forallb_forall in H. specialize (H k Hin). rewrite Nat.eqb_refl in H. discriminate H.
Qed.

(* [comment removed for export] *)
Ltac keep_reg Hse k :=
  let E := fresh "EK" in
  first [ lazymatch type of Hse with WpTac.same_except ?ks _ _ => assert (E := Hse k (notin_b k ks eq_refl)) end;
          lazymatch type of E with ?a = ?b =>
            let b' := eval cbn [WpEngine.rget WpEngine.lget lofR] in b in change (a = b') in E end;
          rewrite E; clear E
        | idtac ].
Ltac keep_regs Hse :=
  keep_reg Hse 1%nat; keep_reg Hse 2%nat; keep_reg Hse 3%nat; keep_reg Hse 4%nat; keep_reg Hse 5%nat; keep_reg Hse 6%nat;
  keep_reg Hse 7%nat; keep_reg Hse 8%nat; keep_reg Hse 9%nat; keep_reg Hse 10%nat; keep_reg Hse 11%nat; keep_reg Hse 12%nat;
  keep_reg Hse 13%nat; keep_reg Hse 14%nat; keep_reg Hse 15%nat; keep_reg Hse 16%nat; keep_reg Hse 17%nat; keep_reg Hse 18%nat;
  keep_reg Hse 19%nat; keep_reg Hse 20%nat; keep_reg Hse 21%nat; keep_reg Hse 22%nat; keep_reg Hse 23%nat; keep_reg Hse 24%nat;
  keep_reg Hse 25%nat; keep_reg Hse 26%nat; keep_reg Hse 27%nat; keep_reg Hse 28%nat; keep_reg Hse 29%nat; keep_reg Hse 30%nat;
  keep_reg Hse 31%nat.

(* [comment removed for export] *)
Ltac getr_leaf H :=
  lazymatch type of H with
  | PropExec.getr ?R ?r = ?v => let a := eval cbv in (PropExec.getr R r) in change (a = v) in H
  end.
Ltac keep_getr Hk r :=
  let E := fresh "EK" in
  first [ lazymatch type of Hk with (forall r0 : reg, ~ In (WpEngine.ridx r0) ?ks -> _) =>
            assert (E := Hk r (notin_b (WpEngine.ridx r) ks eq_refl)) end;
          cbv beta in E;
          lazymatch type of E with ?A = ?B =>
            let a := eval cbv in A in let b := eval cbv in B in change (a = b) in E end;
          subst
        | idtac ].
Ltac keep_getrs Hk :=
  keep_getr Hk (1%bv : reg); keep_getr Hk (2%bv : reg); keep_getr Hk (3%bv : reg); keep_getr Hk (4%bv : reg);
  keep_getr Hk (5%bv : reg); keep_getr Hk (6%bv : reg); keep_getr Hk (7%bv : reg); keep_getr Hk (8%bv : reg);
  keep_getr Hk (9%bv : reg); keep_getr Hk (10%bv : reg); keep_getr Hk (11%bv : reg); keep_getr Hk (12%bv : reg);
  keep_getr Hk (13%bv : reg); keep_getr Hk (14%bv : reg); keep_getr Hk (15%bv : reg); keep_getr Hk (16%bv : reg);
  keep_getr Hk (17%bv : reg); keep_getr Hk (18%bv : reg); keep_getr Hk (19%bv : reg); keep_getr Hk (20%bv : reg);
  keep_getr Hk (21%bv : reg); keep_getr Hk (22%bv : reg); keep_getr Hk (23%bv : reg); keep_getr Hk (24%bv : reg);
  keep_getr Hk (25%bv : reg); keep_getr Hk (26%bv : reg); keep_getr Hk (27%bv : reg); keep_getr Hk (28%bv : reg);
  keep_getr Hk (29%bv : reg); keep_getr Hk (30%bv : reg); keep_getr Hk (31%bv : reg).
