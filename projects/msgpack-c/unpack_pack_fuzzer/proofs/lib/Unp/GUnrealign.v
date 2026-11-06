(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRegroup GRealign.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Import GRealign.
Module GUnrealign.
Section WithPc.
Variable S_PC : int.
Variable L : int.

Fixpoint find_name (fs : list fact) (t : sv) : option int :=
  match fs with
  | [] => None
  | FEq (VP x z) t' :: fs' => if weqb z wzero && sv_eqb t' t then Some x else find_name fs' t
  | _ :: fs' => find_name fs' t
  end.

Fixpoint frames_of (fs : list fact) (k : int) : list (int * w64) :=
  match fs with
  | [] => []
  | FEq (VP n z) (VAlu ALU_AND (VP k' o) (VL mask)) :: fs' =>
      if weqb z wzero && weqb mask MASK32 && PrimInt63.eqb k' k then (n, o) :: frames_of fs' k else frames_of fs' k
  | _ :: fs' => frames_of fs' k
  end.
Fixpoint has_fact (f : fact) (fs : list fact) : bool :=
  match fs with [] => false | g :: fs' => if fact_eqb f g then true else has_fact f fs' end.

Fixpoint find_sliver (st : sstate) (fs : list fact) (k n : int) (room8 : Z) : option (int * int) :=
  match fs with
  | [] => None
  | FEq (VP nb z) (VP k' (W64 true lo)) :: fs' =>
      if weqb z wzero && PrimInt63.eqb k' k
         && match IMap.find nb (s_regs st) with
            | Some rb => PrimInt63.eqb (rg_lo rb) 0%uint63 && sv_eqb (rg_hi rb) (sliver_hi k lo n room8) && rg_w rb
            | None => false
            end
      then Some (nb, lo) else find_sliver st fs' k n room8
  | _ :: fs' => find_sliver st fs' k n room8
  end.

Definition try_frame (st : sstate) (k : int) (rk : region) (rlo rhi : w64) (no : int * w64) : option sstate :=
  let '(n, o) := no in
  match IMap.find n (s_regs st), find_name (s_facts st) (VP n (wlit L)) with
  | Some rn, Some np =>
      match IMap.find np (s_regs st) with
      | Some rp =>
          let oz := w2Zs o in let Lz := to_Z L in let room8 := - keyZ (rg_lo rn) in
          match find_sliver st (s_facts st) k n room8, rg_hi rk with
          | Some (nb, lo), VL hi =>
              let loz := keyZ lo in let o16 := wsub o (wlit 16%uint63) in
              if negb (PrimInt63.eqb k 0%uint63) && negb (PrimInt63.eqb n 0%uint63) && negb (PrimInt63.eqb np 0%uint63) && negb (PrimInt63.eqb nb 0%uint63)
                 && negb (PrimInt63.eqb n k) && negb (PrimInt63.eqb np k) && negb (PrimInt63.eqb nb k)
                 && negb (PrimInt63.eqb np n) && negb (PrimInt63.eqb nb n) && negb (PrimInt63.eqb nb np)
                 && rg_w rk && rg_w rn && rg_w rp
                 && PrimInt63.eqb (rg_lo rk) (zkey (oz + Lz)) && sv_eqb (rg_hi rn) (VL (wlit L))
                 && PrimInt63.eqb (rg_lo rp) 0%uint63 && sv_eqb (rg_hi rp) (pad_hi k o n)
                 && Z.eqb room8 (8 * ((oz - 16 - loz) / 8)) && Z.leb 8 room8
                 && Z.eqb (Lz mod 8) 0 && Z.leb 0 Lz && Z.leb Lz 2040 && Z.ltb (oz + Lz) 0 && Z.leb (- 2 ^ 61) (oz - 64) && Z.ltb loz 0 && Z.leb (- 2 ^ 61) loz
                 && Z.ltb (oz + Lz) (w2Z hi) && negb (wt hi)
                 && nowrap rlo rhi o && nowrap rlo rhi o16
                 && has_fact (FULe (VP n wzero) (VP k o)) (s_facts st) && has_fact (FULe (VP k o16) (VP n wzero)) (s_facts st)
              then Some (GRegroup.regroup st [k; n; np; nb] [(k, Region lo (rg_hi rk) true BGNone (rg_cells rk))] [] (s_next st))
              else None
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.
Fixpoint first_frame (st : sstate) (k : int) (rk : region) (rlo rhi : w64) (l : list (int * w64)) : option sstate :=
  match l with
  | [] => None
  | no :: l' => match try_frame st k rk rlo rhi no with Some st' => Some st' | None => first_frame st k rk rlo rhi l' end
  end.

Definition gunrealign_apply (st : sstate) : option (list sstate) :=
  match getr st X2 with
  | VP k _ =>
      match IMap.find k (s_regs st), find_range (s_facts st) k with
      | Some rk, Some (rlo, rhi) =>
          match rg_bg rk with
          | BGNone => match first_frame st k rk rlo rhi (frames_of (s_facts st) k) with Some st' => Some [st'] | None => None end
          | _ => None
          end
      | _, _ => None
      end
  | _ => None
  end.
Definition gunrealign_contract : contract := Contract S_PC gunrealign_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma find_name_holds : forall E fs t x, Forall (fact_holds E) fs -> find_name fs t = Some x -> den E (VP x wzero) = den E t.
Proof.
  induction fs as [|f fs IH]; intros t x HF H; cbn [find_name] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct f as [| | | |a b| | |]; try exact (IH t x HF' H).
  destruct a as [|x' z| | | | | | | | |]; try exact (IH t x HF' H).
  destruct (weqb z wzero && sv_eqb b t) eqn:C; [|exact (IH t x HF' H)]. injection H as <-.
  apply andb_prop in C as [Z0 EQ]. apply weqb_eq in Z0. apply sv_eqb_eq in EQ. subst z b. exact Hf.
Qed.

Lemma has_fact_holds : forall E fs f, Forall (fact_holds E) fs -> has_fact f fs = true -> fact_holds E f.
Proof.
  induction fs as [|g fs IH]; intros f HF H; cbn [has_fact] in H; [discriminate|].
  inversion HF as [|g' l Hg HF']; subst.
  destruct (fact_eqb f g) eqn:EQ; [apply fact_eqb_eq in EQ; subst g; exact Hg| exact (IH f HF' H)].
Qed.

Lemma find_sliver_some : forall E st fs k n room8 nb lo, Forall (fact_holds E) fs -> find_sliver st fs k n room8 = Some (nb, lo) ->
  den E (VP nb wzero) = den E (VP k (negw lo)) /\
  exists rb, IMap.find nb (s_regs st) = Some rb /\ rg_lo rb = 0%uint63 /\ rg_hi rb = sliver_hi k lo n room8 /\ rg_w rb = true.
Proof.
  induction fs as [|f fs IH]; intros k n room8 nb lo HF H; cbn [find_sliver] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct f as [| | | |a b| | |]; try exact (IH k n room8 nb lo HF' H).
  destruct a as [|x' z| | | | | | | | |]; try exact (IH k n room8 nb lo HF' H).
  destruct b as [|k' w| | | | | | | | |]; try exact (IH k n room8 nb lo HF' H).
  destruct w as [t lo'].
  destruct t; [|exact (IH k n room8 nb lo HF' H)].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|exact (IH k n room8 nb lo HF' H)] end.
  injection H as <- <-.
  apply andb_prop in C as [C RB]. apply andb_prop in C as [Z0 KK]. apply weqb_eq in Z0. apply Uint63.eqb_correct in KK. subst z k'.
  split; [exact Hf|].
  destruct (IMap.find x' (s_regs st)) as [rb|]; [|discriminate RB]. exists rb.
  apply andb_prop in RB as [RB W]. apply andb_prop in RB as [LO HI]. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  split; [reflexivity| split; [exact LO| split; [exact HI| exact W]]].
Qed.

Lemma first_frame_some : forall st k rk rlo rhi l st', first_frame st k rk rlo rhi l = Some st' ->
  exists no, try_frame st k rk rlo rhi no = Some st'.
Proof.
  induction l as [|no l IH]; intros st' H; cbn [first_frame] in H; [discriminate|].
  destruct (try_frame st k rk rlo rhi no) as [s1|] eqn:T; [injection H as <-; exists no; exact T| exact (IH st' H)].
Qed.

Theorem gunrealign_sound : contract_sound segs OPS MP PB gunrealign_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gunrealign_contract c_apply] in HA. unfold gunrealign_apply in HA.
  destruct (getr st X2) as [|k z| | | | | | | | |] eqn:SP; try discriminate HA.
  destruct (IMap.find k (s_regs st)) as [rk|] eqn:Hrk; [|discriminate HA].
  destruct (find_range (s_facts st) k) as [[rlo rhi]|] eqn:FR; [|discriminate HA].
  destruct (rg_bg rk) eqn:BG; try discriminate HA.
  destruct (first_frame st k rk rlo rhi (frames_of (s_facts st) k)) as [st'|] eqn:FF; [|discriminate HA].
  injection HA as <-.
  apply first_frame_some in FF as [[n o] TF]. unfold try_frame in TF.
  destruct (IMap.find n (s_regs st)) as [rn|] eqn:Hrn; [|discriminate TF].
  destruct (find_name (s_facts st) (VP n (wlit L))) as [np|] eqn:FN; [|discriminate TF].
  destruct (IMap.find np (s_regs st)) as [rp|] eqn:Hrp; [|discriminate TF].
  cbv zeta in TF.
  destruct (find_sliver st (s_facts st) k n (- keyZ (rg_lo rn))) as [[nb lo]|] eqn:FS; [|discriminate TF].
  destruct (rg_hi rk) as [hi| | | | | | | | | |] eqn:HI; try discriminate TF.
  match type of TF with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate TF] end.
  injection TF as <-.
  repeat match type of C with (_ && _)%bool = true => let X := fresh "C" in apply andb_prop in C as [C X] end.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  pose proof (find_name_holds E _ _ _ FH FN) as DNP.
  destruct (find_sliver_some E st _ k n _ nb lo FH FS) as (DNB & rb & Hrb & RBlo & RBhi & RBw).
  pose proof (has_fact_holds E _ _ FH C0) as F2. pose proof (has_fact_holds E _ _ FH C1) as F1.
  cbn [fact_holds] in F1, F2.
  pose proof (find_range_sound E _ FH k rlo rhi FR) as RK.
  pose proof (nowrap_sound _ _ _ C3) as NW1. pose proof (nowrap_sound _ _ _ C2) as NW0.
  apply negb_true_iff in C, C30, C29, C28, C27, C26, C25, C24, C23, C22, C4.
  apply Uint63.eqb_correct in C18, C16. apply sv_eqb_eq in C17, C15.
  apply Z.eqb_eq in C14, C12. apply Z.leb_le in C13, C11, C10, C8, C6. apply Z.ltb_lt in C9, C7, C5.
  set (oz := w2Zs o) in *. set (Lz := to_Z L) in *. set (loz := keyZ lo) in *. set (room8 := - keyZ (rg_lo rn)) in *.
  assert (O16 : w2Zs (wsub o (wlit 16%uint63)) = oz - 16).
  { rewrite w2Zs_wsub_small; [reflexivity|]. change (w2Zs (wlit 16%uint63)) with 16. fold oz. unfold two63. lia. }
  rewrite O16 in NW0.
  set (K0 := bv_unsigned (ev E k)) in *. set (N0 := bv_unsigned (ev E n)) in *.
  assert (RK0 : 0 <= K0 < two64) by (pose proof (bv_unsigned_in_range 64 (ev E k)) as X; rewrite bv_modulus_64 in X; exact X).
  assert (RN0 : 0 <= N0 < two64) by (pose proof (bv_unsigned_in_range 64 (ev E n)) as X; rewrite bv_modulus_64 in X; exact X).
  assert (DK : bv_unsigned (den E (VP k o)) = K0 + oz) by (rewrite den_VP; apply Z.mod_small; fold K0 oz; lia).
  assert (DK16 : bv_unsigned (den E (VP k (wsub o (wlit 16%uint63)))) = K0 + oz - 16) by (rewrite den_VP, O16; fold K0; rewrite Z.mod_small by lia; lia).
  assert (DN0 : bv_unsigned (den E (VP n wzero)) = N0) by (rewrite den_VP; change (w2Zs wzero) with 0; fold N0; rewrite Z.add_0_r; apply Z.mod_small; exact RN0).
  rewrite DN0, DK in F1. rewrite DK16, DN0 in F2.
  pose proof (so_reg _ _ _ _ _ _ HS k rk Hrk) as ROk. pose proof (so_reg _ _ _ _ _ _ HS n rn Hrn) as ROn.
  pose proof (so_reg _ _ _ _ _ _ HS np rp Hrp) as ROp. pose proof (so_reg _ _ _ _ _ _ HS nb rb Hrb) as ROb.
  destruct ROk as [Kbst Krange Kvalid Kcells Kin Kbg]. destruct ROn as [_ Nrange Nvalid _ _ _].
  destruct ROp as [_ Prange Pvalid _ _ _]. destruct ROb as [_ Brange Bvalid _ _ _].
  specialize (Krange C). specialize (Kvalid C). specialize (Nrange C30). specialize (Nvalid C30).
  specialize (Prange C29). specialize (Pvalid C29). specialize (Brange C28). specialize (Bvalid C28).
  assert (KC : keyZ (zkey (oz + Lz)) = oz + Lz) by (apply GW.keyZ_of_Z; unfold Mem.two62Z; lia).
  pose proof (keyZ_range (rg_lo rn)) as RLN.
  assert (KN : keyZ (zkey (- room8)) = - room8) by (apply GW.keyZ_of_Z; unfold Mem.two62Z, room8; lia).
  assert (HKZ : hiZ E rk = w2Z hi) by (unfold hiZ; rewrite HI; cbn [den]; apply wbv_unsigned).
  assert (HLZ : hiZ E rn = Lz) by (unfold hiZ; rewrite C17; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  unfold loZ in Krange, Kvalid, Nrange, Nvalid, Prange, Pvalid, Brange, Bvalid.
  rewrite C18, KC, HKZ in Krange, Kvalid. rewrite HLZ in Nrange, Nvalid. fold K0 in Krange, Kvalid. fold N0 in Nrange, Nvalid.
  replace (keyZ (rg_lo rn)) with (- room8) in Nrange, Nvalid by (unfold room8; lia).
  rewrite C16 in Prange, Pvalid. rewrite RBlo in Brange, Bvalid. change (keyZ 0%uint63) with 0 in Prange, Pvalid, Brange, Bvalid.

  assert (LW : w2Zs (wlit L) = Lz) by (unfold w2Zs; cbn [wlit wt]; apply wlit_ok).
  assert (VNP : bv_unsigned (ev E np) = N0 + Lz).
  { apply (f_equal bv_unsigned) in DNP. rewrite !den_VP, LW in DNP. change (w2Zs wzero) with 0 in DNP. fold N0 in DNP.
    rewrite Z.add_0_r in DNP. rewrite (Z.mod_small (N0 + Lz)) in DNP by lia.
    pose proof (bv_unsigned_in_range 64 (ev E np)) as X. rewrite bv_modulus_64 in X. rewrite Z.mod_small in DNP by exact X. exact DNP. }
  assert (HPZ : hiZ E rp = K0 + oz - N0).
  { unfold hiZ. rewrite C15. unfold pad_hi. cbn [den alu64 alu]. rewrite bv_sub_unsigned. fold (den E (VP k o)) (den E (VP n wzero)). rewrite DK, DN0.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. lia. }
  rewrite VNP, HPZ in Prange, Pvalid.

  assert (LOZ : w2Zs (negw lo) = loz) by (apply w2Zs_negw; fold loz; lia).
  assert (RMZ : w2Zs (negw (zkey (- room8))) = - room8) by (rewrite w2Zs_negw; rewrite KN; lia).
  set (A := (K0 + loz) mod two64).
  assert (RA : 0 <= A < two64) by (apply Z.mod_pos_bound; unfold two64; lia).
  assert (VNB : bv_unsigned (ev E nb) = A).
  { apply (f_equal bv_unsigned) in DNB. rewrite !den_VP, LOZ in DNB. change (w2Zs wzero) with 0 in DNB. fold K0 in DNB.
    rewrite Z.add_0_r in DNB. pose proof (bv_unsigned_in_range 64 (ev E nb)) as X. rewrite bv_modulus_64 in X. rewrite Z.mod_small in DNB by exact X. exact DNB. }
  assert (HBZ : hiZ E rb = (N0 - room8 - A) mod two64).
  { unfold hiZ. rewrite RBhi. unfold sliver_hi. cbn [den alu64 alu]. rewrite bv_sub_unsigned.
    fold (den E (VP n (negw (zkey (- room8))))) (den E (VP k (negw lo))). rewrite !den_VP, RMZ, LOZ. fold N0 K0. fold A.
    rewrite (Z.mod_small (N0 + - room8)) by lia. unfold bv_wrap. rewrite bv_modulus_64. first [reflexivity | f_equal; lia]. }
  rewrite VNB, HBZ in Brange, Bvalid.
  assert (AB : A <= N0 - room8 /\ (N0 - room8 - A) mod two64 = N0 - room8 - A).
  { destruct (Z_lt_ge_dec (N0 - room8 - A) 0) as [NEG|NN].
    - exfalso. replace (N0 - room8 - A) with ((N0 - room8 - A + two64) + (-1) * two64) in Brange by lia.
      rewrite Z.mod_add, Z.mod_small in Brange by (unfold two64 in *; lia). lia.
    - split; [lia| apply Z.mod_small; lia]. }
  destruct AB as [AB1 AB2]. rewrite AB2 in Brange, Bvalid.
  assert (AV : A = K0 + loz).
  { unfold A. destruct (Z_lt_ge_dec (K0 + loz) 0) as [NEG|NN]; [| apply Z.mod_small; clear - RK0 NN C7; lia].
    exfalso. assert (X : A = K0 + loz + two64).
    { unfold A. symmetry. apply (Z.mod_unique_pos (K0 + loz) two64 (-1) (K0 + loz + two64)); unfold two64 in *; clear - RK0 NEG C6; lia. }
    unfold two64 in *. lia. }
  rewrite AV in *.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ _) HMP _).
  apply (GRegroup.regroup_sound segs OPS E st ms model [k; n; np; nb] _ _ _ HS).
  - cbn [map fst]. constructor; [intros []| constructor].
  - intros j rj [X|[]]. injection X as <- <-. split; [exact C| left; left; reflexivity].
  - intros j IN. cbn [In] in IN. destruct IN as [<-|[<-|[<-|[<-|[]]]]]; assumption.
  -
    intros j rj [X|[]]. injection X as <- <-. constructor.
    + exact Kbst.
    + intros _. fold K0. unfold loZ, hiZ. cbn [rg_lo rg_hi den]. rewrite wbv_unsigned. fold loz. lia.
    + intros _ a Ha. fold K0 in Ha. unfold loZ, hiZ in Ha. cbn [rg_lo rg_hi den] in Ha. rewrite wbv_unsigned in Ha. fold loz in Ha. cbn [rg_w].
      destruct (Z_lt_ge_dec a (N0 - room8)) as [L1|G1].
      { destruct (Bvalid a ltac:(lia)) as (V1 & V2 & V3). split; [exact V1| split; [intros _; apply V2; exact RBw| exact V3]]. }
      destruct (Z_lt_ge_dec a (N0 + Lz)) as [L2|G2].
      { destruct (Nvalid a ltac:(lia)) as (V1 & V2 & V3). split; [exact V1| split; [intros _; apply V2; exact C20| exact V3]]. }
      destruct (Z_lt_ge_dec a (K0 + oz + Lz)) as [L3|G3].
      { destruct (Pvalid a ltac:(lia)) as (V1 & V2 & V3). split; [exact V1| split; [intros _; apply V2; exact C19| exact V3]]. }
      destruct (Kvalid a ltac:(lia)) as (V1 & V2 & V3). split; [exact V1| split; [intros _; apply V2; exact C21| exact V3]].
    + intros g gr G1. cbn [rg_cells] in G1. exact (Kcells g gr G1).
    + intros g gr c i G1 IC Hi. cbn [rg_cells] in G1. destruct (Kin g gr c i G1 IC Hi) as [P1 P2]. cbv zeta in P1, P2 |- *.
      split; [|intros X; rewrite C in X; discriminate X].
      intros _. specialize (P1 C). unfold loZ in P1. rewrite C18, KC, HKZ in P1. unfold loZ, hiZ. cbn [rg_lo rg_hi den]. rewrite wbv_unsigned. fold loz. lia.
    + intros o' H1 H2 U. unfold bg_byte. cbn [rg_bg]. exact I.
  -
    intros j rj a [X|[]] Ha. injection X as <- <-. unfold GRegroup.rng in Ha. fold K0 in Ha. unfold loZ, hiZ in Ha. cbn [rg_lo rg_hi den] in Ha. rewrite wbv_unsigned in Ha. fold loz in Ha.
    cbn [rg_w]. unfold GRegroup.rng.
    destruct (Z_lt_ge_dec a (N0 - room8)) as [L1|G1].
    { exists nb, rb. split; [right; right; right; left; reflexivity|]. split; [exact Hrb|]. split; [| intros _; exact RBw].
      unfold loZ. rewrite RBlo, VNB, HBZ, AB2. change (keyZ 0%uint63) with 0. lia. }
    destruct (Z_lt_ge_dec a (N0 + Lz)) as [L2|G2].
    { exists n, rn. split; [right; left; reflexivity|]. split; [exact Hrn|]. split; [| intros _; exact C20].
      fold N0. rewrite HLZ. unfold loZ. replace (keyZ (rg_lo rn)) with (- room8) by (unfold room8; lia). lia. }
    destruct (Z_lt_ge_dec a (K0 + oz + Lz)) as [L3|G3].
    { exists np, rp. split; [right; right; left; reflexivity|]. split; [exact Hrp|]. split; [| intros _; exact C19].
      unfold loZ. rewrite C16, VNP, HPZ. change (keyZ 0%uint63) with 0. lia. }
    exists k, rk. split; [left; reflexivity|]. split; [exact Hrk|]. split; [| intros _; exact C21].
    fold K0. unfold loZ. rewrite C18, KC, HKZ. lia.
  - intros j1 r1 j2 r2 a [X|[]] [Y|[]] NE. injection X as <- <-. injection Y as <- <-. exfalso. apply NE. reflexivity.
  - constructor.
Qed.
End Sound.

End WithPc.
End GUnrealign.
