(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "list"; "true"; "option"; "nat"; "andb"; "length"; "prod"; "app"; "None"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "cell"; "sv"; "sobj"; "sstate"; "c_off"; "ob_cells"; "c_val"; "c_width"; "ob_base"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_objs"; "SLit"; "ob_dflt"; "odefault"; "sprop"; "DImage"; "DList"; "DRom"; "DZero"; "dflt_writable"; "tfact"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "pfacts"; "cell_equiv"; "odefault_eqb"; "cells_entailed_pf"; "entails_cheap"; "fact_entailed_d"; "lit_shift_eqb"; "nodupN"; "select"; "arr_entailed_pf"; "cell_shift_eqb"; "complement"; "entails"; "entails_fr"; "entails_pfx"; "find_entailed_pf"; "obj_entailed_pf"; "objs_entailed_pf"; "pf_d0"; "pf_dg"; "pf_f"; "witnesses_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "sv_equiv"; "itv0"; "same_atoms"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast"; "zip_all"; "cells_entailed_pf_l"; "small_lit"; "all_small"; "entails_pfx_f"; "witnesses_pf_f"; "cell_equiv_f"; "cell_equiv_s"; "cells_entailed_pf_e"; "entails_p_f"; "objs_entailed_pf_f"; "small_off"; "entails_f"; "entails_fr_f"; "entails_fr_p_f"; "find_entailed_pf_f"; "obj_entailed_pf_f"; "obj_entailed_same_pf_f"; "obj_entailed_shift_pf_f"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "add"; "ltb"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "forallb_lazy"; "existsb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "obj_subst"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "entails_p"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import XformFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import DigFastA.
Import ListNotations.
Open Scope Z_scope.

Definition small_lit (z : Z) : bool := ltac2:(tb__ "0|0|
S0S0L_;S55Z0Vz;A2S57Vz;Z100000000A2S1X0x2").

Lemma sv_equiv_lit_ne : ltac2:(tb__ "0|1|
S24S24S23S0S43R2A1S3A3M0G0S23S0S54R4R3A2S1A3S23S0S3dS19R5A1S19R4A1A2S1A3F_;F_;F_;Fy;Fx;").
Proof.
  intros x y Hx Hy Hne. unfold small_lit in Hx, Hy.
  destruct (0 <=? x) eqn:Hx0; [|discriminate]. destruct (0 <=? y) eqn:Hy0; [|discriminate].
  apply Z.leb_le in Hx0, Hy0. apply Z.ltb_lt in Hx, Hy. apply Z.eqb_neq in Hne.
  unfold sv_equiv. cbn [sv_eqb]. rewrite (proj2 (Z.eqb_neq x y) Hne). cbn [orb].
  unfold same_atoms, same_atoms0. cbn [atoms_of remove_atoms].
  apply Z.eqb_neq. intros H. apply Z.mod_divide in H; [|discriminate].
  destruct H as [k Hk]. change (2 ^ 64) with 18446744073709551616 in Hk. lia.
Qed.

Definition cell_equiv_f (cL c : cell) : bool := ltac2:(tb__ "0|9|
SdS0Lx;M0S10VcL;A1S24G0S10Vc;A1S24S0S0L_;M1S54R2R1A2G1S54S13VcL;A1S13Vc;A1A2S3dS12VcL;A1S12Vc;A1A2S1X0x2G1S43R2A1G1S43R1A1S1S28VcL;Vc;A2M2X0x2G2X0x2X0x2Lx;S25G2Li;M3S5dSdSdG2Lb;La;M4Lop;M5G5S5eG4Lop;M6G6S0S26SdG2La;Lw;Lsgn;M7S25SdS24G2Lk;Li;Ll;M8Xdx8Ly;G3G5G5G6G6G7G8Xdx8").

Lemma cell_equiv_f_eq : ltac2:(tb__ "0|0|
ScScS23S0S47R2R1A2S28R2R1A2A3Fc;FcL;").
Proof.
  intros [oL wL vL] [o w v]. unfold cell_equiv_f. cbn [c_off c_width c_val].
  destruct oL as [y| | | | | | |]; try reflexivity.
  destruct o as [x| | | | | | |]; try reflexivity.
  destruct (y =? x) eqn:E.
  - unfold cell_equiv. cbn [c_off c_width c_val].
    assert (Ho : sv_equiv (SLit y) (SLit x) = true) by (unfold sv_equiv; cbn [sv_eqb]; rewrite E; reflexivity).
    rewrite Ho. reflexivity.
  - destruct (small_lit y) eqn:Sy; [|reflexivity]. destruct (small_lit x) eqn:Sx; [|reflexivity].
    unfold cell_equiv. cbn [c_off c_width c_val]. rewrite (sv_equiv_lit_ne y x Sy Sx E). reflexivity.
Qed.

Definition small_off (c : cell) : bool := ltac2:(tb__ "0|3|
SdS0Lx;S10Vc;A1S24S43R1A1Ly;S25S1Li;S5dSdSdS1Lb;La;M0Lop;M1G1S5eG0Lop;M2G2S0S26SdS1La;Lw;Lsgn;S25SdS24S1Lk;Li;Ll;Xdx8").
Definition all_small (l : list cell) : bool := forallb_lazy small_off l.
Definition cell_equiv_s (cL c : cell) : bool := ltac2:(tb__ "0|8|
SdS0Lx;M0S10VcL;A1S24G0S10Vc;A1S24S0S0L_;M1S54R2R1A2G1S54S13VcL;A1S13Vc;A1A2S3dS12VcL;A1S12Vc;A1A2S1X0x2S1X0x2Lx;S25S1Li;M2S5dSdSdS1Lb;La;M3Lop;M4G4S5eG3Lop;M5G5S0S26SdS1La;Lw;Lsgn;M6S25SdS24S1Lk;Li;Ll;M7Xdx8Ly;G2G4G4G5G5G6G7Xdx8").
Lemma cell_equiv_s_eq : ltac2:(tb__ "0|1|
ScScS23S0S4cR2A1S3A3M0G0S23S0S48R4R3A2S28R4R3A2A3F_;F_;Fc;FcL;").
Proof.
  intros cL c HL Hc. rewrite <- cell_equiv_f_eq. unfold cell_equiv_s, cell_equiv_f. unfold small_off in HL, Hc.
  destruct (c_off cL) as [y| | | | | | |]; try discriminate. destruct (c_off c) as [x| | | | | | |]; try discriminate.
  rewrite HL, Hc. reflexivity.
Qed.
Lemma all_small_in : ltac2:(tb__ "0|0|
S2ScA1ScS23S0S44R2A1S3A3S5fScR2R3A3S23S0S4cR3A1S3A3F_;F_;Fc;Fl;").
Proof. intros l c H Hin. unfold all_small in H. rewrite forallb_lazy_eq in H. exact (proj1 (forallb_forall _ _) H c Hin). Qed.

Fixpoint zip_all (f : cell -> cell -> bool) (l1 l2 : list cell) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: t1, b :: t2 => if f a b then zip_all f t1 t2 else false
  | _, _ => false
  end.

Lemma zip_all_fe : ltac2:(tb__ "0|1|
ScScS0F_;F_;S2ScA1M0G0S23S0S41R3R2R1A3S3A3G0S23S0S60ScScS61ScScR7R1R2A2LcL;S9ScR2R5A3A3Lc;R3A3S3A3Fpre;F_;Fl2;Fl1;Ff;").
Proof.
  intros f l1. induction l1 as [|a t1 IH]; intros [|b t2] H pre; cbn [zip_all] in H; try discriminate; [reflexivity|].
  destruct (f a b) eqn:E; [|discriminate]. cbn [forallb]. apply andb_true_intro. split.
  - rewrite existsb_app. cbn [existsb]. rewrite E. rewrite orb_true_r. reflexivity.
  - specialize (IH t2 H (pre ++ [a])). rewrite <- app_assoc in IH. exact IH.
Qed.
Lemma zip_all_fe' : ltac2:(tb__ "0|1|
ScScS0F_;F_;S2ScA1M0G0S23S0S41R3R2R1A3S3A3G0S23S0S60ScScS61ScScR7R2R1A2Lc;S9ScR2R4A3A3LcL;R4A3S3A3Fpre;F_;Fl2;Fl1;Ff;").
Proof.
  intros f l1. induction l1 as [|a t1 IH]; intros [|b t2] H pre; cbn [zip_all] in H; try discriminate; [reflexivity|].
  destruct (f a b) eqn:E; [|discriminate]. cbn [forallb]. apply andb_true_intro. split.
  - rewrite existsb_app. cbn [existsb]. rewrite E. rewrite orb_true_r. reflexivity.
  - specialize (IH t2 H (pre ++ [b])). rewrite <- app_assoc in IH. exact IH.
Qed.

Definition cells_entailed_pf_l (pf : pfacts) (ceq : cell -> cell -> bool) (oL oT : sobj) : bool := ltac2:(tb__ "0|8|
S41Vceq;S11VoL;A1M0S11VoT;A1M1A3S0S0S0L_;M2S0S0Lz;M3R1S3S59ScScS5aScScVceq;R1R2A2LcL;G0A3Lc;G1A3X0x2S1bS0Lx;S1aVoT;A1S21S1aVoL;A1M4A1G2S29G4S20A2G3R1S3S59ScScS5aScScVceq;R2R1A2Lc;G1A3LcL;G0A3M5X0x2M6S1X0x2G2S29G4S1dA2G6S1X0x2S25G2S29G4S1eR1A1A2G3R2S3G5X0x2M7S1X0x2Ll;S25G2S29G4S1fR1A1A2G7S1X0x2Ll;S24SdS2S8S24S24A2A1S2S22A1S30Vpf;VoL;R4R3R2R1A6LtmplT;LfldsT;LcntT;LeszT;X1bx6S1X0x2Tz;").

Lemma existsb_ext_in : forall {A} (f g : A -> bool) l, (forall a, In a l -> f a = g a) -> existsb f l = existsb g l.
Proof.
  intros A f g l H. induction l as [|a t IH]; cbn [existsb]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma forallb_ext_in : forall {A} (f g : A -> bool) l, (forall a, In a l -> f a = g a) -> forallb f l = forallb g l.
Proof.
  intros A f g l H. induction l as [|a t IH]; cbn [forallb]; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.
Lemma zip_all_ext_in : ltac2:(tb__ "0|3|
ScScS0F_;F_;M0G0S2ScA1M1G1ScScS5fScR2R4A3M2G2S23S0R8R4R3A2R7R4R3A2A3F_;F_;Fb;Fa;S23S0S41R5R3R2A3S41R4R3R2A3A3F_;Fl2;Fl1;Fg;Ff;").
Proof.
  intros f g l1. induction l1 as [|a t1 IH]; intros [|b t2] H; cbn [zip_all]; try reflexivity.
  rewrite (H a b (or_introl eq_refl) (or_introl eq_refl)). destruct (g a b); [|reflexivity].
  apply IH. intros x y Hx Hy. apply H; right; assumption.
Qed.

Lemma cells_entailed_pf_l_eq : ltac2:(tb__ "0|2|
S27ScScS0Fx0;Fx;M0G0SeSeScScS5fScR2S11R4A1A3M1G1S23S0R7R4R3A2R8R4R3A2A3F_;F_;Fb;Fa;S23S0S42R6R4R3R2A4S2aR6R5R3R2A4A3F_;FoT;FoL;Fceq';Fceq;Fpf;").
Proof.
  intros pf ceq ceq' oL oT H. unfold cells_entailed_pf_l, cells_entailed_pf. cbv zeta.
  rewrite (zip_all_ext_in ceq' ceq _ _ H).
  assert (E1 : forallb_lazy (fun c => existsb_lazy (fun cL => ceq' cL c) (ob_cells oL)) (ob_cells oT)
             = forallb (fun c => existsb (fun cL => ceq cL c) (ob_cells oL)) (ob_cells oT)).
  { rewrite forallb_lazy_eq. apply forallb_ext_in. intros c Hc. rewrite existsb_lazy_eq. apply existsb_ext_in. intros a Ha. apply H; assumption. }
  assert (E2 : forallb_lazy (fun cL => existsb_lazy (fun c => ceq' cL c) (ob_cells oT)) (ob_cells oL)
             = forallb (fun cL => existsb (fun c => ceq cL c) (ob_cells oT)) (ob_cells oL)).
  { rewrite forallb_lazy_eq. apply forallb_ext_in. intros a Ha. rewrite existsb_lazy_eq. apply existsb_ext_in. intros c Hc. apply H; assumption. }
  rewrite E1, E2. clear E1 E2 H.
  destruct (zip_all ceq (ob_cells oL) (ob_cells oT)) eqn:Z.
  - pose proof (zip_all_fe ceq _ _ Z []) as Z1. pose proof (zip_all_fe' ceq _ _ Z []) as Z2. cbn [app] in Z1, Z2.
    rewrite Z1, Z2. cbn [andb].
    destruct (ob_dflt oT); try reflexivity;
      match goal with |- (if ?b then true else false) = _ => destruct b; reflexivity end.
  - destruct (forallb (fun c => existsb (fun cL => ceq cL c) (ob_cells oL)) (ob_cells oT)); cbn [andb]; [|reflexivity].
    destruct (ob_dflt oT); try reflexivity;
      match goal with |- (if ?b then _ else false) = _ => destruct b; reflexivity end.
Qed.

Definition cells_entailed_pf_e (pf : pfacts) (oL oT : sobj) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0G0S44S11VoL;A1A1S44S11VoT;A1A1S1X0x2S42Vpf;S48VoL;VoT;A4S42Vpf;S47VoL;VoT;A4X0x2").
Lemma cells_entailed_pf_e_eq : ltac2:(tb__ "0|0|
S27SeSeS23S0S49R3R2R1A3S2aR3S28R2R1A4A3FoT;FoL;Fpf;").
Proof.
  intros. unfold cells_entailed_pf_e.
  destruct (all_small (ob_cells oL)) eqn:SL; [destruct (all_small (ob_cells oT)) eqn:ST|].
  - apply cells_entailed_pf_l_eq. intros a b Ha Hb. apply cell_equiv_s_eq; [exact (all_small_in _ _ SL Ha) | exact (all_small_in _ _ ST Hb)].
  - apply cells_entailed_pf_l_eq. intros a b _ _. apply cell_equiv_f_eq.
  - apply cells_entailed_pf_l_eq. intros a b _ _. apply cell_equiv_f_eq.
Qed.

Definition obj_entailed_same_pf_f (pf : pfacts) (oL oT : sobj) : bool := ltac2:(tb__ "0|1|
S0S0L_;M0S3dS14VoL;A1S14VoT;A1A2G0S3dS16VoL;A1S16VoT;A1A2G0S3dS15VoL;A1S15VoT;A1A2S49Vpf;VoL;VoT;A3S1X0x2S1X0x2S1X0x2").
Definition obj_entailed_shift_pf_f (pf : pfacts) (oL oT : sobj) : bool := ltac2:(tb__ "0|2|
S4S24A1S0Lx;S3fS14VoT;A1S14VoL;A1M0A2S24S0S0L_;M1S2dR1S16VoL;A1S16VoT;A1A3G1S2dR1S15VoL;A1S15VoT;A1A3S8S24S24A2S0Lx;S3eS3bVpf;A1G0A2S24S24G1S6S6S55Z0S56R2R3A2A2S57S56R1R3A2S58Z2Z40A2A2A2S55R2R1A2A2S42Vpf;S31R3A1VoL;VoT;A4S1X0x2Lh;Ll;X8x1S1X0x2S1X0x2Lc;S1X4x2").
Definition obj_entailed_pf_f (pf : pfacts) (oL oT : sobj) : bool := ltac2:(tb__ "0|0|
S0S0L_;S52Vpf;VoL;VoT;A3S3S53Vpf;VoL;VoT;A3X0x2").
Lemma obj_entailed_pf_f_eq : ltac2:(tb__ "0|0|
S27SeSeS23S0S51R3R2R1A3S37R3R2R1A3A3FoT;FoL;Fpf;").
Proof.
  intros. unfold obj_entailed_pf_f, obj_entailed_pf, obj_entailed_same_pf_f, obj_entailed_same_pf,
    obj_entailed_shift_pf_f, obj_entailed_shift_pf.
  rewrite cells_entailed_pf_e_eq.
  destruct (same_atoms (ob_base oT) (ob_base oL)) as [c|]; [|reflexivity].
  rewrite (cells_entailed_pf_l_eq pf (cell_shift_eqb c) (cell_shift_eqb c) oL oT (fun _ _ _ _ => eq_refl)). reflexivity.
Qed.

Fixpoint find_entailed_pf_f (pf : pfacts) (objsL : list sobj) (oT : sobj) (n : nat) : option nat :=
  match objsL with
  | [] => None
  | o :: t => if obj_entailed_pf_f pf o oT then Some n else find_entailed_pf_f pf t oT (S n)
  end.
Lemma find_entailed_pf_f_eq : ltac2:(tb__ "0|0|
S27S2SeA1SeS5S23S4S5A1S50R4R3R2R1A4S36R4R3R2R1A4A3Fn;FoT;FobjsL;Fpf;").
Proof. intros pf objsL oT. induction objsL as [|o t IH]; intros n; cbn [find_entailed_pf_f find_entailed_pf]; [reflexivity|]. rewrite obj_entailed_pf_f_eq, IH. reflexivity. Qed.

Fixpoint witnesses_pf_f (pf : pfacts) (objsL : list sobj) (objsT : list sobj) : option (list nat) :=
  match objsT with
  | [] => Some []
  | oT :: t => match find_entailed_pf_f pf objsL oT 0, witnesses_pf_f pf objsL t with
               | Some n, Some ns => Some (n :: ns)
               | _, _ => None
               end
  end.
Lemma witnesses_pf_f_eq : ltac2:(tb__ "0|1|
S27S2SeA1M0G0S23S4S2S5A1A1S46R3R2R1A3S3cR3R2R1A3A3FobjsT;FobjsL;Fpf;").
Proof. intros pf objsL objsT. induction objsT as [|o t IH]; cbn [witnesses_pf_f witnesses_pf]; [reflexivity|]. rewrite find_entailed_pf_f_eq, IH. reflexivity. Qed.

Definition objs_entailed_pf_f (pf : pfacts) (objsL objsT : list sobj) : bool := ltac2:(tb__ "0|2|
S0S0L_;S65S7SeVobjsT;A2S7SeVobjsL;A2A2M0S4S2S5A1M1A1S0Lx;S46Vpf;VobjsL;VobjsT;A3G1S6S2eR1A1G0A2Lns;S1X4x2S1X0x2").
Lemma objs_entailed_pf_f_eq : ltac2:(tb__ "0|1|
S27S2SeA1M0G0S23S0S4bR3R2R1A3S38R3R2R1A3A3FobjsT;FobjsL;Fpf;").
Proof. intros. unfold objs_entailed_pf_f, objs_entailed_pf. rewrite witnesses_pf_f_eq. reflexivity. Qed.

Definition entails_pfx_f (pf : pfacts) (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|3|
S0S0L_;M0S4bVpf;S18VL;A1S62SeSeS5cVs;A1S18VT;A1A4A3G0S59S1cS2cS39Vpf;A1S17VL;A1M1Vs;A3S17VT;A1M2A3S3S59S1cS2cS3aVpf;A1G1Vs;A3G2A3X0x2S1X0x2").
Lemma entails_pfx_f_eq : ltac2:(tb__ "0|0|
S27SfSfS5bS23S0S45R4R3R2R1A4S35R4R3R2R1A4A3Fs;FT;FL;Fpf;").
Proof. intros. unfold entails_pfx_f, entails_pfx. rewrite objs_entailed_pf_f_eq, !forallb_lazy_eq. reflexivity. Qed.

Definition entails_p_f (pf : pfacts) (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|0|
S0S0L_;S2bVL;VT;Vs;A3S45Vpf;VL;VT;Vs;A4S1X0x2").
Lemma entails_p_f_eq : ltac2:(tb__ "0|0|
S27SfSfS5bS23S0S4aR4R3R2R1A4S64R4R3R2R1A4A3Fs;FT;FL;Fpf;").
Proof. intros. unfold entails_p_f, entails_p. rewrite entails_pfx_f_eq. reflexivity. Qed.

Definition entails_f (L T : sstate) (s : wsub) : bool := ltac2:(tb__ "0|0|
S4aS63S17VL;A1A1VL;VT;Vs;A4").
Lemma entails_f_eq : ltac2:(tb__ "0|0|
SfSfS5bS23S0S4dR3R2R1A3S33R3R2R1A3A3Fs;FT;FL;").
Proof. intros. unfold entails_f. rewrite entails_p_f_eq, mk_pf_f_eq. reflexivity. Qed.

Definition entails_fr_p_f (pf : pfacts) (L T : sstate) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|6|
S4S2S5A1M0A1S4S2SeA1M1A1M2Lx;S46Vpf;S18VL;A1M3S62SeSeS5cVs;A1S18VT;A1A4A3G0S7SeG3A2S5S0G2L_;S6S6S2eR2A1S60S5S5S66R1R2A2Li;R2A3A2S0S0L_;S2bS40VL;S2fG3R2A2A2M4VT;Vs;A3S45Vpf;G4VT;Vs;A4S1X0x2A2SbG1S2fG3S32R2R1A2A2A2SaG1A1M5X0x2Tn;Lns;G5X4x2").
Definition entails_fr_f (L T : sstate) (s : wsub) : option (list sobj) := ltac2:(tb__ "0|0|
S4fS63S17VL;A1A1VL;VT;Vs;A4").
Lemma entails_fr_f_eq : ltac2:(tb__ "0|0|
SfSfS5bS23S4S2SeA1A1S4eR3R2R1A3S34R3R2R1A3A3Fs;FT;FL;").
Proof.
  intros. unfold entails_fr_f, entails_fr_p_f, entails_fr. cbv zeta. rewrite mk_pf_f_eq, witnesses_pf_f_eq.
  destruct (witnesses_pf (mk_pf (ss_facts L)) (ss_objs L) (map (obj_subst s) (ss_objs T))) as [ns|]; [|reflexivity].
  rewrite entails_pfx_f_eq. reflexivity.
Qed.
