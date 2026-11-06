(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChFix FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChWv.

Module FxChDirDefs.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxFacts.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint lbytes_ok (img : tree Z) (fs : list fact) (rgs : list region) (b : lin) (bs : list Z) (j : Z) : bool :=
  match bs with
  | [] => true
  | x :: r => match load_at img fs rgs (laddc b j) SZ1 false with
              | Some (Some l) => (lin_eqb l (lconst x) && lbytes_ok img fs rgs b r (j + 1))%bool
              | _ => false
              end
  end.
Definition readdir_args_ok (S : sst) : bool :=
  match a7c S, arg S 0 with
  | Some c7, Some c0 =>
      let h1 := snd (irange (s_facts S) (argl S 1)) in let h2 := snd (irange (s_facts S) (argl S 2)) in
      (Z.eqb c7 63 && Z.eqb c0 3 && Z.leb h2 TASK_SIZE && Z.leb (h1 + h2) TASK_SIZE)%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition writev2_okz (img : tree Z) (S : sst) (B0 : lin) (ch : Z) (bs : list Z) (off : lin) : option lin :=
  let fs := s_facts S in let rgs := s_rgs S in
  match a7c S, arg S 0, arg S 2, load_at img fs rgs (argl S 1) SZ8 false, load_at img fs rgs (laddc (argl S 1) 8) SZ8 false,
        load_at img fs rgs (laddc (argl S 1) 16) SZ8 false, load_at img fs rgs (laddc (argl S 1) 24) SZ8 false with
  | Some c7, Some c0, Some c2, Some (Some b), Some (Some len), Some (Some z1), Some (Some z2) =>
      let n := Z.of_nat (length bs) in
      if (Z.eqb c7 66 && Z.eqb c0 ch && (Z.eqb ch 1 || Z.eqb ch 2) && Z.eqb c2 2 &&
          lin_eqb b (ladd off B0) && lin_eqb len (laddc (lneg off) n) && lin_eqb z1 (lconst 0) && lin_eqb z2 (lconst 0) &&
          lbytes_ok img fs rgs B0 bs 0 &&
          Z.leb 0 (fst (irange fs off)) && Z.ltb (snd (irange fs off)) n && Z.leb 1 n && Z.leb n 1073741824 &&
          Z.leb (snd (irange fs B0) + n) TASK_SIZE && Z.leb (snd (irange fs (argl S 1)) + 32) TASK_SIZE &&
          lwf (s_next S) off && lwf (s_next S) (argl S 1) && lwf (s_next S) B0)%bool
      then Some len else None
  | _, _, _, _, _, _, _ => None
  end.
Definition dot_z : list Z := [46; 0].
End FxChDirDefs.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC.FxChDirDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition srec : Type := (lin * lin * nat)%type.
(* [comment removed for export] *)
Definition sbytes_ok (sarg : nat -> list byte) (E : valu) (m0 : word -> option byte) (r : srec) : Prop :=
  let '(b, l, j) := r in
  uE E l = Z.of_nat (length (sarg j)) /\
  (forall i, 0 <= i < uE E l -> m0 (Z_to_bv 64 (uE E b + i)) = Some (nth (Z.to_nat i) (sarg j) (Z_to_bv 8 0))).
(* [comment removed for export] *)
Fixpoint lit_bytes_ok (img : tree Z) (fs : list fact) (rgs : list region) (B0 : Z) (bs : list Z) (j : Z) : bool :=
  match bs with
  | [] => true
  | x :: r => match load_at img fs rgs (lconst (B0 + j)) SZ1 false with
              | Some (Some l) => (lin_eqb l (lconst x) && lit_bytes_ok img fs rgs B0 r (j + 1))%bool
              | _ => false
              end
  end.

Inductive bkind : Type := BFull | BPreArg | BPre | BSuf.
Inductive wsrc : Type :=
| WBuf (B0 : lin) (kd : bkind) (rc : nat)    (* [comment removed for export] *)
| WArg (rc : nat)                            (* [comment removed for export] *)
| WLit (d : Z)                               (* [comment removed for export] *)
| WEmpty.                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rsep_above (fs : list fact) (b : lin) (lh : Z) (R : region) : bool :=
  let '(lo, hi) := irange fs (lsub (rg_base R) b) in (Z.leb lh lo && Z.ltb hi (2 ^ 62))%bool.
Definition gap_ok (fs : list fact) (rgs : list region) (b : lin) (lh : Z) (R : region) : bool :=
  (existsb (fun P1 => match lin_off b (rg_base P1), is_const (rg_size P1) with
                      | Some e1, Some s1 => (Z.eqb e1 s1 && Z.ltb 0 e1 && Z.ltb e1 (2 ^ 62) && Z.ltb (snd (irange fs (rg_base P1)) + e1) two64)%bool
                      | _, _ => false end) rgs &&
   existsb (fun P3 => match lin_off (rg_base P3) b with
                      | Some e3 => (Z.leb lh e3 && Z.ltb e3 (size_lo fs R) && Z.ltb 0 (size_lo fs P3) && Z.ltb e3 (2 ^ 62))%bool
                      | None => false end) rgs)%bool.

(* [comment removed for export] *)
Definition frz_cov (fs : list fact) (b l : lin) (p : lin * lin) : bool :=
  let '(lo1, hi1) := irange fs (lsub b (fst p)) in let '(lo2, hi2) := irange fs (lsub (snd p) (ladd (lsub b (fst p)) l)) in
  (Z.leb 0 lo1 && Z.ltb hi1 (2 ^ 62) && Z.leb 0 lo2 && Z.ltb hi2 (2 ^ 62))%bool.
Definition rec_mem_ref (S : sst) (M : smodel) (b l : lin) : bool :=
  (existsb (frz_cov (s_facts S) b l) (sm_frz M) ||
   (existsb (fun p => (lin_eqb (fst p) b && lin_eqb (snd p) l)%bool) (sm_own M) &&
    Z.leb (snd (irange (s_facts S) b) + snd (irange (s_facts S) l)) 0x800000000000 &&
    forallb (fun R => (lin_eqb (rg_base R) (ladd b l) || rgs_sep (s_facts S) b (snd (irange (s_facts S) l)) R ||
                       rsep_above (s_facts S) b (snd (irange (s_facts S) l)) R ||
                       gap_ok (s_facts S) (s_rgs S) b (snd (irange (s_facts S) l)) R)%bool) (s_rgs S)))%bool.
(* [comment removed for export] *)
Definition rec_mem (S : sst) (M : smodel) (b l : lin) : bool :=
  if existsb_lz (frz_cov (s_facts S) b l) (sm_frz M) then true else
  if existsb_lz (fun p => if lin_eqb (fst p) b then lin_eqb (snd p) l else false) (sm_own M) then
    let lh := snd (irange (s_facts S) l) in
    let br := irange (s_facts S) b in      (* [comment removed for export] *)
    if Z.leb (snd br + lh) 0x800000000000 then
      let e := ladd b l in
      forallb (fun R => if lin_eqb (rg_base R) e then true else if rgs_sepA (s_facts S) b br lh R then true
                        else if rsep_above (s_facts S) b lh R then true else gap_ok (s_facts S) (s_rgs S) b lh R) (s_rgs S)
    else false
  else false.
Lemma forallb_ext_w : forall {A : Type} (f g : A -> bool) (l : list A), (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros A f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.
Lemma rec_mem_eq : forall S M b l, rec_mem S M b l = rec_mem_ref S M b l.
Proof.
  intros S M b l. unfold rec_mem, rec_mem_ref. rewrite !existsb_lz_eq. cbv zeta.
  destruct (existsb (frz_cov (s_facts S) b l) (sm_frz M)); [reflexivity|]. cbn [orb].
  change (existsb (fun p => if lin_eqb (fst p) b then lin_eqb (snd p) l else false) (sm_own M))
    with (existsb (fun p => (lin_eqb (fst p) b && lin_eqb (snd p) l)%bool) (sm_own M)).
  destruct (existsb (fun p => (lin_eqb (fst p) b && lin_eqb (snd p) l)%bool) (sm_own M)); [|reflexivity]. cbn [andb].
  destruct (Z.leb (snd (irange (s_facts S) b) + snd (irange (s_facts S) l)) 140737488355328); [|reflexivity].
  apply forallb_ext_w. intros R.
  destruct (lin_eqb (rg_base R) (ladd b l)); [reflexivity|]. rewrite rgs_sepA_eq. destruct (rgs_sep (s_facts S) b (snd (irange (s_facts S) l)) R); [reflexivity|].
  destruct (rsep_above (s_facts S) b (snd (irange (s_facts S) l)) R); reflexivity.
Qed.
Definition rec_ok (S : sst) (M : smodel) (recs : list srec) (rc : nat) (b l : lin) (j : nat) : bool :=
  match nth_error recs rc with
  | Some (b', l', j') => (lin_eqb b' b && lin_eqb l' l && Nat.eqb j' j && rec_mem S M b l)%bool
  | None => false
  end.
Definition wbase (recs : list srec) (F : wsrc) : lin :=
  match F with
  | WBuf B0 _ _ => B0
  | WArg rc => match nth_error recs rc with Some (b, _, _) => b | None => lconst 0 end
  | WLit d => lconst d
  | WEmpty => lconst 0
  end.
Definition wsrc_ok (img : tree Z) (S : sst) (M : smodel) (recs : list srec) (pre suf : list Z) (j : nat) (lj : lin) (F : wsrc) : bool :=
  let fs := s_facts S in let rgs := s_rgs S in let P := Z.of_nat (length pre) in
  match F with
  | WBuf B0 BPre _ => lbytes_ok img fs rgs B0 pre 0
  | WBuf B0 BSuf _ => lbytes_ok img fs rgs B0 suf 0
  | WBuf B0 BPreArg rc => (lbytes_ok img fs rgs B0 pre 0 && rec_ok S M recs rc (laddc B0 P) lj j)%bool
  | WBuf B0 BFull rc => (lbytes_ok img fs rgs B0 pre 0 && rec_ok S M recs rc (laddc B0 P) lj j &&
                         lbytes_ok img fs rgs (ladd (laddc B0 P) lj) suf 0)%bool
  | WArg rc => match nth_error recs rc with Some (b, _, _) => rec_ok S M recs rc b lj j | None => false end
  | WLit d => lit_bytes_ok img fs rgs d suf 0
  | WEmpty => true
  end.
(* [comment removed for export] *)
Definition wspanZ (P S L : Z) (F : wsrc) : Z * Z :=
  match F with
  | WBuf _ BFull _ => (0, P + L + S)
  | WBuf _ BPreArg _ => (0, P + L)
  | WBuf _ BPre _ => (0, P)
  | WBuf _ BSuf _ => (P + L, S)
  | WArg _ => (P, L)
  | WLit _ => (P + L, S)
  | WEmpty => (0, 0)
  end.

Definition msgb (sarg : nat -> list byte) (pre suf : list Z) (j : nat) : list byte :=
  List.map (Z_to_bv 8) pre ++ sarg j ++ List.map (Z_to_bv 8) suf.

Lemma zbv_mod : forall a b, a mod two64 = b mod two64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. exact H. Qed.

Section Src.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Himg : img_ok segs img.
Variable sarg : nat -> list byte.

#[using="Himg sarg"] Lemma lbytes_ok_rd1' : forall E m fs rgs (b : lin) bs j, Forall (rg_ok segs E m) rgs -> Forall (fact_ok E) fs ->
  lbytes_ok img fs rgs b bs j = true ->
  forall i, (i < length bs)%nat -> rd1 segs m (lden E (laddc b (j + Z.of_nat i))) = Some (Z_to_bv 8 (nth i bs 0)).
Proof. LiaFast.lf_pins (fun (Himg sarg : LiaFast.U) => LiaFast.u0).
  intros E m fs rgs b bs. induction bs as [|x r IH]; intros j HG HF Hok i Hi; cbn [length] in Hi; [lia|].
  cbn [lbytes_ok] in Hok.
  destruct (load_at img fs rgs (laddc b j) SZ1 false) as [[l|]|] eqn:Hl; try discriminate.
  apply andb_prop in Hok as [Hx Hr]. apply lin_eqb_eq in Hx. subst l.
  destruct i as [|i].
  - destruct (load_at_sound segs E img fs rgs _ SZ1 false _ m Himg HG HF Hl) as (bs1 & Hrd & Hv).
    specialize (Hv (lconst x) eq_refl). rewrite ov_rdn in Hrd. cbn [nbytes rdn] in Hrd.
    destruct (match m (lden E (laddc b j)) with Some b0 => Some b0 | None => seg_rom segs (lden E (laddc b j)) end) as [b1|] eqn:Hb1;
      [|discriminate].
    injection Hrd as <-. rewrite ld1_byte, lden_lconst in Hv.
    replace (j + Z.of_nat 0) with j by lia. unfold rd1. rewrite Hb1. f_equal. cbn [nth].
    apply bv_eq. apply (f_equal bv_unsigned) in Hv. rewrite !Z_to_bv_unsigned in Hv. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range _ b1) as Hb. change (bv_modulus 8) with 256 in Hb.
    unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in Hv. change (bv_modulus 8) with 256.
    rewrite (Z.mod_small (bv_unsigned b1)) in Hv by lia.
    rewrite (Zmod_div_mod 256 (2 ^ 64) x) by (first [lia | exists 72057594037927936; reflexivity]). rewrite Hv. symmetry. apply Z.mod_small. lia.
  - cbn [nth]. replace (j + Z.of_nat (Datatypes.S i)) with ((j + 1) + Z.of_nat i) by lia. exact (IH (j + 1) HG HF Hr i ltac:(lia)).
Qed.
#[using="Himg sarg"] Lemma bytes_ok_rd1' : forall E m fs rgs B0 bs j, Forall (rg_ok segs E m) rgs -> Forall (fact_ok E) fs ->
  lit_bytes_ok img fs rgs B0 bs j = true ->
  forall i, (i < length bs)%nat -> rd1 segs m (Z_to_bv 64 (B0 + j + Z.of_nat i)) = Some (Z_to_bv 8 (nth i bs 0)).
Proof. LiaFast.lf_pins (fun (Himg sarg : LiaFast.U) => LiaFast.u0).
  intros E m fs rgs B0 bs. induction bs as [|x r IH]; intros j HG HF Hok i Hi; cbn [length] in Hi; [lia|].
  cbn [lit_bytes_ok] in Hok.
  destruct (load_at img fs rgs (lconst (B0 + j)) SZ1 false) as [[l|]|] eqn:Hl; try discriminate.
  apply andb_prop in Hok as [Hx Hr]. apply lin_eqb_eq in Hx. subst l.
  destruct i as [|i].
  - destruct (load_at_sound segs E img fs rgs _ SZ1 false _ m Himg HG HF Hl) as (bs1 & Hrd & Hv).
    specialize (Hv (lconst x) eq_refl). rewrite ov_rdn in Hrd. cbn [nbytes rdn] in Hrd.
    destruct (match m (lden E (lconst (B0 + j))) with Some b => Some b | None => seg_rom segs (lden E (lconst (B0 + j))) end) as [b1|] eqn:Hb1;
      [|discriminate].
    injection Hrd as <-. rewrite ld1_byte, lden_lconst in Hv. rewrite lden_lconst in Hb1.
    rewrite Z.add_0_r. unfold rd1. rewrite Hb1. f_equal. cbn [nth].
    apply bv_eq. apply (f_equal bv_unsigned) in Hv. rewrite !Z_to_bv_unsigned in Hv. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range _ b1) as Hb. change (bv_modulus 8) with 256 in Hb.
    unfold bv_wrap in *. change (bv_modulus 64) with (2 ^ 64) in Hv. change (bv_modulus 8) with 256.
    rewrite (Z.mod_small (bv_unsigned b1)) in Hv by lia.
    rewrite (Zmod_div_mod 256 (2 ^ 64) x) by (first [lia | exists 72057594037927936; reflexivity]). rewrite Hv. symmetry. apply Z.mod_small. lia.
  - cbn [nth]. replace (B0 + j + Z.of_nat (Datatypes.S i)) with (B0 + (j + 1) + Z.of_nat i) by lia. exact (IH (j + 1) HG HF Hr i ltac:(lia)).
Qed.

(* [comment removed for export] *)
#[using="sarg"] Lemma rec_mem_pt : forall E S M ms model b l, DEN segs LIMIT model0 mem0 E S M ms model -> rec_mem S M b l = true ->
  snd (irange (s_facts S) l) < 2 ^ 62 ->
  forall i, 0 <= i < uE E l -> mrestrict (Hof E M model) (ms_mem ms) (Z_to_bv 64 (uE E b + i)) = mem0 (Z_to_bv 64 (uE E b + i)).
Proof. LiaFast.lf_pins (fun (sarg : LiaFast.U) => LiaFast.u0).
  intros E S M ms model b l Hd Hrm Hlhi i Hi.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG & HDJ & HF & _).
  pose proof (irange_sound E (s_facts S) l HF) as Rl. fold (uE E l) in Rl.
  pose proof (uE_range E b) as RB. pose proof (uE_range E l) as RL.
  rewrite rec_mem_eq in Hrm. unfold rec_mem_ref in Hrm. apply orb_prop in Hrm as [Hfz|Hown].
  - apply existsb_exists in Hfz as (p & Hp & Hc). unfold frz_cov in Hc.
    destruct (irange (s_facts S) (lsub b (fst p))) as [lo1 hi1] eqn:Hr1.
    destruct (irange (s_facts S) (lsub (snd p) (ladd (lsub b (fst p)) l))) as [lo2 hi2] eqn:Hr2.
    repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?Hq] end.
    apply Z.leb_le in Hc. repeat match goal with Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx end.
    pose proof (irange_sound E (s_facts S) (lsub b (fst p)) HF) as R1. rewrite Hr1 in R1. cbn [fst snd] in R1.
    pose proof (irange_sound E (s_facts S) (lsub (snd p) (ladd (lsub b (fst p)) l)) HF) as R2. rewrite Hr2 in R2. cbn [fst snd] in R2.
    fold (uE E (lsub b (fst p))) in R1. fold (uE E (lsub (snd p) (ladd (lsub b (fst p)) l))) in R2.
    pose proof (uE_range E (fst p)) as RP. pose proof (uE_range E (snd p)) as RS.
    (* [comment removed for export] *)
    assert (Hpt0 : uE E (snd p) > 0 -> uE E (fst p) + uE E (snd p) <= 0x800000000000).
    { intros Hsz. destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd p Hp (uE E (fst p) + uE E (snd p) - 1) ltac:(lia)) as ((_ & X) & _). lia. }
    assert (Hd0 : uE E (ladd (lsub b (fst p)) l) = uE E (lsub b (fst p)) + uE E l).
    { unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E (lsub b (fst p))) (uE E l).
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small.
      assert (X1 : uE E l < 2 ^ 62) by lia. assert (X2 : uE E (lsub b (fst p)) < 2 ^ 62) by lia.
      pose proof (uE_range E (lsub b (fst p))). unfold two64 in *. lia. }
    destruct (small_diff E b (fst p) lo1 hi1 R1) as [[Hl1 He1]|[Hl1 He1]]; [|exfalso].
    + assert (Hd1 : uE E (ladd (lsub b (fst p)) l) = uE E b - uE E (fst p) + uE E l) by (rewrite Hd0, <- He1; reflexivity).
      destruct (small_diff E (snd p) (ladd (lsub b (fst p)) l) lo2 hi2 R2) as [[Hl2 He2]|[Hl2 He2]]; rewrite Hd1 in Hl2, He2; [|exfalso; unfold two64 in *; lia].
      assert (Hin : uE E (fst p) <= uE E b + i < uE E (fst p) + uE E (snd p)) by lia.
      destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd p Hp (uE E b + i) Hin) as (Htp & _ & Hm).
      unfold mrestrict. rewrite (frz_hidden_false segs LIMIT model0 mem0 E S M ms model _ Hd Htp). exact Hm.
    + destruct (small_diff E (snd p) (ladd (lsub b (fst p)) l) lo2 hi2 R2) as [[Hl2 He2]|[Hl2 He2]].
      * (* [comment removed for export] *)
        assert (Hnz : uE E (snd p) > 0).
        { destruct (Z.eq_dec (uE E (snd p)) 0) as [Hz|Hz]; [|lia]. exfalso. rewrite Hd0 in Hl2, He2. unfold two64 in *. lia. }
        specialize (Hpt0 Hnz). unfold two64 in *. lia.
      * rewrite Hd0 in Hl2, He2. unfold two64 in *. lia.
  - apply andb_prop in Hown as [Hown Hsep]. apply andb_prop in Hown as [Hex Hbd]. apply Z.leb_le in Hbd.
    apply existsb_exists in Hex as (p & Hp & Hpe). apply andb_prop in Hpe as [E1 E2]. apply lin_eqb_eq in E1, E2.
    pose proof (irange_sound E (s_facts S) b HF) as Rb. fold (uE E b) in Rb.
    assert (Hin : uE E (fst p) <= uE E b + i < uE E (fst p) + uE E (snd p)) by (rewrite E1, E2; lia).
    destruct (dn_own _ _ _ _ _ _ _ _ _ Hd p Hp (uE E b + i) Hin) as [Hv Hm].
    unfold mrestrict. rewrite Hv. apply Hm.
    unfold outside. apply Forall_forall. intros R HR. rewrite forallb_forall in Hsep.
    rewrite Forall_forall in HG. destruct (HG R HR) as (Hrs & Hrw & _).
    pose proof (Hsep R HR) as HsR. apply orb_prop in HsR as [HsR|Hgap]; [apply orb_prop in HsR as [HsR|Habv]|].
    3:{ (* [comment removed for export] *)
      rewrite u_small64 by (unfold two64; lia).
      apply andb_prop in Hgap as [Hp1 Hp3]. apply existsb_exists in Hp1 as (P1 & HP1 & Hc1). apply existsb_exists in Hp3 as (P3 & HP3 & Hc3).
      destruct (lin_off b (rg_base P1)) as [e1|] eqn:Ho1; [|discriminate]. destruct (is_const (rg_size P1)) as [s1|] eqn:Hs1; [|discriminate].
      destruct (lin_off (rg_base P3) b) as [e3|] eqn:Ho3; [|discriminate].
      repeat match goal with Hx : ((_ && _)%bool = true) |- _ => apply andb_prop in Hx as [Hx ?Hy] end.
      repeat match goal with
             | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
             | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
             | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx end.
      subst s1.
      destruct (HG P1 HP1) as (Hrs1 & Hrw1 & _). destruct (HG P3 HP3) as (Hrs3 & Hrw3 & _).
      pose proof (size_lo_sound E (s_facts S) R HF) as HszR. pose proof (size_lo_sound E (s_facts S) P3 HF) as HszP3.
      pose proof (uE_range E (rg_base P1)) as RP1. pose proof (uE_range E (rg_base P3)) as RP3. pose proof (uE_range E (rg_base R)) as RR.
      (* [comment removed for export] *)
      assert (HA1 : uE E b = uE E (rg_base P1) + e1).
      { pose proof (irange_sound E (s_facts S) (rg_base P1) HF) as RbP1. fold (uE E (rg_base P1)) in RbP1.
        unfold uE. apply (lin_off_u E b (rg_base P1) e1 Ho1). unfold uE in *. lia. }
      assert (HS1 : rsz E P1 = e1).
      { unfold rsz. destruct (is_const_sound E _ e1 Hs1) as [Hcv _]. rewrite Hcv. apply u_small64. unfold two64. lia. }
      assert (HA3 : uE E (rg_base P3) = uE E b + e3).
      { unfold uE. apply (lin_off_u E (rg_base P3) b e3 Ho3). unfold uE, two64 in *. lia. }
      (* [comment removed for export] *)
      destruct (In_nth_error _ _ HR) as (k & Hk). destruct (In_nth_error _ _ HP1) as (k1 & Hk1). destruct (In_nth_error _ _ HP3) as (k3 & Hk3).
      destruct (Nat.eq_dec k k1) as [->|Hne1].
      { rewrite Hk1 in Hk. injection Hk as <-. right. rewrite HS1. unfold uE in *. lia. }
      destruct (Nat.eq_dec k k3) as [->|Hne3].
      { rewrite Hk3 in Hk. injection Hk as <-. left. unfold uE in *. lia. }
      pose proof (rgs_disj_nth E (s_rgs S) k k1 R P1 HDJ Hne1 Hk Hk1) as D1.
      pose proof (rgs_disj_nth E (s_rgs S) k k3 R P3 HDJ Hne3 Hk Hk3) as D3.
      unfold rg_disj in D1, D3. rewrite HS1 in D1. fold (uE E (rg_base R)) (uE E (rg_base P1)) (uE E (rg_base P3)) in D1, D3.
      destruct (Z_lt_le_dec (uE E b + i) (uE E (rg_base R))) as [Y|Y]; [left; unfold uE in *; exact Y|].
      destruct (Z_lt_le_dec (uE E b + i) (uE E (rg_base R) + rsz E R)) as [Y2|Y2]; [|right; unfold uE in *; exact Y2].
      exfalso. lia. }
    2:{ (* [comment removed for export] *)
      rewrite u_small64 by (unfold two64; lia). left.
      unfold rsep_above in Habv. destruct (irange (s_facts S) (lsub (rg_base R) b)) as [lo hi] eqn:Hir.
      apply andb_prop in Habv as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      pose proof (irange_sound E (s_facts S) (lsub (rg_base R) b) HF) as Rd. rewrite Hir in Rd. cbn [fst snd] in Rd.
      fold (uE E (lsub (rg_base R) b)) in Rd.
      destruct (small_diff E (rg_base R) b lo hi Rd) as [[Hl He]|[Hl He]]; unfold uE in *; [lia|].
      exfalso. pose proof (uE_range E (rg_base R)) as RR. unfold uE, two64 in *. lia. }
    apply orb_prop in HsR as [Hadj|HsR].
    { (* [comment removed for export] *)
      apply lin_eqb_eq in Hadj. left. rewrite u_small64 by (unfold two64; lia).
      assert (Hbl : bv_unsigned (lden E (rg_base R)) = uE E b + uE E l).
      { rewrite Hadj, lden_ladd, bv_add_unsigned. fold (uE E b) (uE E l). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        apply Z.mod_small. unfold two64. lia. }
      rewrite Hbl. unfold uE in *. lia. }
    pose proof (rgs_sep_sound E (s_facts S) b (snd (irange (s_facts S) l)) R HF ltac:(lia) ltac:(lia) Hrw HsR) as X.
    rewrite u_small64 by (unfold two64; lia). unfold uE in X. specialize (X (bv_unsigned (lden E b) + i)).
    destruct (Z_lt_le_dec (bv_unsigned (lden E b) + i) (bv_unsigned (lden E (rg_base R)))) as [Y|Y]; [left; exact Y|].
    destruct (Z_lt_le_dec (bv_unsigned (lden E b) + i) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [Y2|Y2]; [|right; exact Y2].
    exfalso. apply X; [lia|]. unfold uE in *. lia.
Qed.
End Src.

Lemma msg_pre : forall sarg pre suf j x, 0 <= x < Z.of_nat (length pre) ->
  nth (Z.to_nat x) (msgb sarg pre suf j) (Z_to_bv 8 0) = Z_to_bv 8 (nth (Z.to_nat x) pre 0).
Proof.
  intros sarg pre suf j x Hx. unfold msgb. rewrite app_nth1 by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.
Lemma msg_arg : forall sarg pre suf j x, Z.of_nat (length pre) <= x < Z.of_nat (length pre) + Z.of_nat (length (sarg j)) ->
  nth (Z.to_nat x) (msgb sarg pre suf j) (Z_to_bv 8 0) = nth (Z.to_nat (x - Z.of_nat (length pre))) (sarg j) (Z_to_bv 8 0).
Proof.
  intros sarg pre suf j x Hx. unfold msgb. rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
  rewrite app_nth1 by lia. f_equal. lia.
Qed.
Lemma msg_suf : forall sarg pre suf j x,
  Z.of_nat (length pre) + Z.of_nat (length (sarg j)) <= x < Z.of_nat (length pre) + Z.of_nat (length (sarg j)) + Z.of_nat (length suf) ->
  nth (Z.to_nat x) (msgb sarg pre suf j) (Z_to_bv 8 0) = Z_to_bv 8 (nth (Z.to_nat (x - Z.of_nat (length pre) - Z.of_nat (length (sarg j)))) suf 0).
Proof.
  intros sarg pre suf j x Hx. unfold msgb. rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
  rewrite app_nth2 by lia. rewrite map_nth. f_equal. f_equal. lia.
Qed.
Lemma length_msgb : forall sarg pre suf j, length (msgb sarg pre suf j) = (length pre + length (sarg j) + length suf)%nat.
Proof. intros. unfold msgb. rewrite !length_app, !length_map. lia. Qed.

Section Src2.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Himg : img_ok segs img.
Variable sarg : nat -> list byte.

#[using="Type"] Lemma rec_ok_pt : forall E S M ms model recs rc b l j, DEN segs LIMIT model0 mem0 E S M ms model ->
  Forall (sbytes_ok sarg E mem0) recs -> rec_ok S M recs rc b l j = true -> snd (irange (s_facts S) l) < 2 ^ 62 ->
  uE E l = Z.of_nat (length (sarg j)) /\
  forall i, 0 <= i < uE E l -> rd1 segs (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 (uE E b + i)) = Some (nth (Z.to_nat i) (sarg j) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model recs rc b l j Hd Hrec Hok Hlhi. unfold rec_ok in Hok.
  destruct (nth_error recs rc) as [[[b' l'] j']|] eqn:Hn; [|discriminate].
  repeat match type of Hok with ((_ && _)%bool = true) => apply andb_prop in Hok as [Hok ?Hq] end.
  apply lin_eqb_eq in Hok. match goal with Hx : lin_eqb l' l = true |- _ => apply lin_eqb_eq in Hx; subst l' end.
  match goal with Hx : Nat.eqb j' j = true |- _ => apply Nat.eqb_eq in Hx; subst j' end. subst b'.
  match goal with Hx : rec_mem S M b l = true |- _ => rename Hx into Hrm end.
  rewrite Forall_forall in Hrec. destruct (Hrec (b, l, j) (nth_error_In _ _ Hn)) as [Hlen Hby].
  split; [exact Hlen|]. intros i Hi. unfold rd1. rewrite (rec_mem_pt segs LIMIT model0 mem0 sarg E S M ms model b l Hd Hrm Hlhi i Hi).
  rewrite (Hby i Hi). reflexivity.
Qed.

#[using="Himg"] Theorem wsrc_sound : forall E S M ms model recs pre suf j lj F,
  DEN segs LIMIT model0 mem0 E S M ms model ->
  Forall (sbytes_ok sarg E mem0) recs ->
  uE E lj = Z.of_nat (length (sarg j)) -> snd (irange (s_facts S) lj) < 2 ^ 62 ->
  wsrc_ok img S M recs pre suf j lj F = true ->
  forall x, 0 <= x < snd (wspanZ (Z.of_nat (length pre)) (Z.of_nat (length suf)) (uE E lj) F) ->
    rd1 segs (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 (uE E (wbase recs F) + x)) =
      Some (nth (Z.to_nat (fst (wspanZ (Z.of_nat (length pre)) (Z.of_nat (length suf)) (uE E lj) F) + x)) (msgb sarg pre suf j) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros E S M ms model recs pre suf j lj F Hd Hrec HLj Hlhi Hok x Hx.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG & _ & HF & _).
  set (H := Hof E M model) in *. set (mm := mrestrict H (ms_mem ms)).
  change (Forall (rg_ok segs E (ms_mem (restrict H ms))) (s_rgs S)) in HG.
  set (P := Z.of_nat (length pre)) in *. set (Sl := Z.of_nat (length suf)) in *. set (L := uE E lj) in *.
  pose proof (uE_range E lj) as RL. fold L in RL.
  assert (Hpre : forall B0, lbytes_ok img (s_facts S) (s_rgs S) B0 pre 0 = true -> forall y, 0 <= y < P ->
            rd1 segs mm (Z_to_bv 64 (uE E B0 + y)) = Some (nth (Z.to_nat y) (msgb sarg pre suf j) (Z_to_bv 8 0))).
  { intros B0 Hb y Hy. rewrite msg_pre by exact Hy.
    pose proof (lbytes_ok_rd1' segs img Himg sarg E _ _ _ B0 pre 0 HG HF Hb (Z.to_nat y) ltac:(unfold P in Hy; lia)) as X.
    rewrite lden_laddc, Z2Nat.id in X by lia. replace (0 + y) with y in X by lia. exact X. }
  assert (Hsuf : forall B1 o, lbytes_ok img (s_facts S) (s_rgs S) B1 suf 0 = true -> o = P + L ->
            forall y, 0 <= y < Sl -> rd1 segs mm (Z_to_bv 64 (uE E B1 + y)) = Some (nth (Z.to_nat (o + y)) (msgb sarg pre suf j) (Z_to_bv 8 0))).
  { intros B1 o Hb Ho y Hy. subst o. rewrite msg_suf by (unfold P, L, Sl in *; lia).
    pose proof (lbytes_ok_rd1' segs img Himg sarg E _ _ _ B1 suf 0 HG HF Hb (Z.to_nat y) ltac:(unfold Sl in Hy; lia)) as X.
    rewrite lden_laddc, Z2Nat.id in X by lia. replace (0 + y) with y in X by lia.
    transitivity (Some (Z_to_bv 8 (nth (Z.to_nat y) suf 0))); [exact X|]. do 2 f_equal. f_equal. unfold P, L in *. lia. }
  destruct F as [B0 [| | |] rc | rc | d | ]; cbn [wsrc_ok wspanZ wbase fst snd] in Hok, Hx |- *.
  - (* [comment removed for export] *)
    apply andb_prop in Hok as [Hok Hs3]. apply andb_prop in Hok as [Hs1 Hs2].
    destruct (Z_lt_le_dec x P) as [X1|X1]; [rewrite Z.add_0_l; exact (Hpre B0 Hs1 x ltac:(lia))|].
    destruct (Z_lt_le_dec x (P + L)) as [X2|X2].
    + destruct (rec_ok_pt E S M ms model recs rc (laddc B0 P) lj j Hd Hrec Hs2 Hlhi) as [_ Hpt].
      specialize (Hpt (x - P) ltac:(fold L; lia)). rewrite Z.add_0_l, msg_arg by (fold P; rewrite <- HLj; fold L; lia). fold P.
      fold mm in Hpt. rewrite <- Hpt. f_equal. apply zbv_mod. unfold uE at 2. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. fold (uE E B0). rewrite Zplus_mod_idemp_l. f_equal. lia.
    + rewrite Z.add_0_l.
      pose proof (Hsuf (ladd (laddc B0 P) lj) (P + L) Hs3 eq_refl (x - P - L) ltac:(lia)) as X.
      replace (P + L + (x - P - L)) with x in X by lia. rewrite <- X. f_equal. apply zbv_mod.
      unfold uE at 2. rewrite lden_ladd, bv_add_unsigned, lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. fold (uE E B0) (uE E lj). fold L.
      rewrite (Zplus_mod_idemp_l (uE E B0 + P) L two64). rewrite Zplus_mod_idemp_l. f_equal. lia.
  - (* [comment removed for export] *)
    apply andb_prop in Hok as [Hs1 Hs2].
    destruct (Z_lt_le_dec x P) as [X1|X1]; [rewrite Z.add_0_l; exact (Hpre B0 Hs1 x ltac:(lia))|].
    destruct (rec_ok_pt E S M ms model recs rc (laddc B0 P) lj j Hd Hrec Hs2 Hlhi) as [_ Hpt].
    specialize (Hpt (x - P) ltac:(fold L; lia)). rewrite Z.add_0_l, msg_arg by (fold P; rewrite <- HLj; fold L; lia). fold P.
    fold mm in Hpt. rewrite <- Hpt. f_equal. apply zbv_mod. unfold uE at 2. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. fold (uE E B0). rewrite Zplus_mod_idemp_l. f_equal. lia.
  - (* [comment removed for export] *) rewrite Z.add_0_l. exact (Hpre B0 Hok x Hx).
  - (* [comment removed for export] *) exact (Hsuf B0 (P + L) Hok eq_refl x Hx).
  - (* [comment removed for export] *)
    destruct (nth_error recs rc) as [[[b l'] j']|] eqn:Hn; [|discriminate].
    destruct (rec_ok_pt E S M ms model recs rc b lj j Hd Hrec Hok Hlhi) as [_ Hpt].
    specialize (Hpt x ltac:(fold L; lia)). rewrite msg_arg by (fold P; rewrite <- HLj; fold L; lia). fold P.
    transitivity (Some (nth (Z.to_nat x) (sarg j) (Z_to_bv 8 0))); [exact Hpt|]. f_equal. f_equal. f_equal. lia.
  - (* [comment removed for export] *)
    pose proof (bytes_ok_rd1' segs img Himg sarg E _ _ _ d suf 0 HG HF Hok (Z.to_nat x) ltac:(unfold Sl in Hx; lia)) as X.
    rewrite Z2Nat.id in X by lia. fold mm in X.
    rewrite msg_suf by (unfold P, L, Sl in *; lia).
    replace (Z_to_bv 64 (uE E (lconst d) + x)) with (Z_to_bv 64 (d + 0 + x)).
    + transitivity (Some (Z_to_bv 8 (nth (Z.to_nat x) suf 0))); [exact X|]. do 2 f_equal. f_equal. unfold P, L in *. lia.
    + apply zbv_mod. unfold uE. rewrite lden_lconst, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Zplus_mod_idemp_l. f_equal. lia.
  - lia.
Qed.
End Src2.

(* [comment removed for export] *)
Definition wspanL (P Sl : Z) (lj : lin) (F : wsrc) : lin * lin :=
  match F with
  | WBuf _ BFull _ => (lconst 0, laddc lj (P + Sl))
  | WBuf _ BPreArg _ => (lconst 0, laddc lj P)
  | WBuf _ BPre _ => (lconst 0, lconst P)
  | WBuf _ BSuf _ => (laddc lj P, lconst Sl)
  | WArg _ => (lconst P, lj)
  | WLit _ => (laddc lj P, lconst Sl)
  | WEmpty => (lconst 0, lconst 0)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint irange_dgo (fs0 : list fact) (q : lin) (fs : list fact) : option (Z * Z) :=
  match fs with
  | [] => None
  | FRange fl flo fhi :: r =>
      let '(lo2, hi2) := irange fs0 (lsub q fl) in
      if (Z.leb 0 flo && Z.leb 0 lo2 && Z.ltb fhi (2 ^ 62) && Z.ltb hi2 (2 ^ 62))%bool then Some (flo + lo2, fhi + hi2) else irange_dgo fs0 q r
  | _ :: r => irange_dgo fs0 q r
  end.
Definition irange_d (fs : list fact) (q : lin) : Z * Z :=
  let '(lo, hi) := irange fs q in
  if (Z.leb 0 lo && Z.ltb hi (2 ^ 62))%bool then (lo, hi) else match irange_dgo fs q fs with Some p => p | None => (lo, hi) end.
Lemma irange_dgo_sound : forall E fs0 q fs lo hi, Forall (fact_ok E) fs0 -> Forall (fact_ok E) fs ->
  irange_dgo fs0 q fs = Some (lo, hi) -> lo <= uE E q <= hi.
Proof.
  intros E fs0 q fs. induction fs as [|f r IH]; intros lo hi H0 Hf Hs; cbn [irange_dgo] in Hs; [discriminate|].
  inversion Hf as [|? ? Hfl Hr']; subst.
  destruct f as [c a b tk | fl flo fhi | l k rr | l m v | x v j | x bs]; try exact (IH lo hi H0 Hr' Hs).
  destruct (irange fs0 (lsub q fl)) as [lo2 hi2] eqn:Hr.
  destruct (Z.leb 0 flo && Z.leb 0 lo2 && Z.ltb fhi (2 ^ 62) && Z.ltb hi2 (2 ^ 62))%bool eqn:Hc; [|exact (IH lo hi H0 Hr' Hs)].
  injection Hs as <- <-.
  repeat match type of Hc with ((_ && _)%bool = true) => apply andb_prop in Hc as [Hc ?Hq] end.
  repeat match goal with Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx end.
  cbn [fact_ok] in Hfl. fold (uE E fl) in Hfl.
  pose proof (irange_sound E fs0 (lsub q fl) H0) as R2. rewrite Hr in R2. cbn [fst snd] in R2. fold (uE E (lsub q fl)) in R2.
  rewrite u_lsub_mod in R2. pose proof (uE_range E q) as Rq. pose proof (uE_range E fl) as Rf.
  destruct (Z_le_gt_dec (uE E fl) (uE E q)) as [Hle|Hgt].
  - rewrite Z.mod_small in R2 by (unfold two64 in *; lia). lia.
  - exfalso. replace (uE E q - uE E fl) with ((uE E q - uE E fl + two64) + (-1) * two64) in R2 by ring.
    rewrite Z_mod_plus_full, Z.mod_small in R2 by (unfold two64 in *; lia). unfold two64 in *. lia.
Qed.
Lemma irange_d_sound : forall E fs q lo hi, Forall (fact_ok E) fs -> irange_d fs q = (lo, hi) -> 0 <= lo -> lo <= uE E q <= hi.
Proof.
  intros E fs q lo hi HF H Hlo. unfold irange_d in H. pose proof (irange_sound E fs q HF) as R.
  destruct (irange fs q) as [lo0 hi0] eqn:Hr. cbn [fst snd] in R.
  destruct (Z.leb 0 lo0 && Z.ltb hi0 (2 ^ 62))%bool eqn:Hl; [injection H as <- <-; exact R|].
  destruct (irange_dgo fs q fs) as [[lo' hi']|] eqn:Hd; [injection H as <- <-; exact (irange_dgo_sound E fs q fs _ _ HF HF Hd)|].
  injection H as <- <-. exact R.
Qed.

Definition iov_src_ok0 (fs : list fact) (recs : list srec) (P Sl : Z) (lj : lin) (b l off0 : lin) (F : wsrc) : bool :=
  let '(o, T) := wspanL P Sl lj F in
  let '(lo1, hi1) := irange_d fs (lsub off0 o) in let '(lo2, hi2) := irange_d fs (lsub (ladd o T) off0) in
  (lin_eqb b (ladd (wbase recs F) (lsub off0 o)) && lin_eqb l (lsub (ladd o T) off0) &&
   Z.leb 0 lo1 && Z.ltb hi1 (2 ^ 40) && Z.leb 0 lo2 && Z.ltb hi2 (2 ^ 40) &&
   (Z.leb (snd (irange fs (wbase recs F)) + snd (irange fs T)) TASK_SIZE ||
    (Z.ltb (snd (irange fs (wbase recs F))) (2 ^ 62) && Z.ltb (snd (irange fs T)) (2 ^ 62) &&
     Z.leb (snd (irange fs (ladd (wbase recs F) T))) TASK_SIZE)))%bool.
Definition iov_src_ok (fs : list fact) (recs : list srec) (P Sl : Z) (lj : lin) (b l off0 : lin) (F : wsrc) : bool :=
  match F with
  | WEmpty => (lin_eqb l (lconst 0) && lin_eqb off0 (laddc lj (P + Sl)) && Z.leb (snd (irange fs b)) TASK_SIZE)%bool
  | _ => iov_src_ok0 fs recs P Sl lj b l off0 F
  end.
Definition len_rec (recs : list srec) (lj : lin) (j : nat) : bool := existsb (fun r => (lin_eqb (snd (fst r)) lj && Nat.eqb (snd r) j)%bool) recs.

Lemma map_nth_firstn_skipn : forall (l : list byte) k n d, (k + n <= length l)%nat ->
  List.map (fun i => nth (k + i) l d) (seq 0 n) = firstn n (skipn k l).
Proof.
  intros l k n d Hk. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
  - rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n) as [_|Hc]; [|lia]. cbn [option_map]. rewrite Nat.add_0_l.
    rewrite nth_error_firstn. destruct (Nat.ltb_spec i n) as [_|Hc]; [|lia]. rewrite nth_error_skipn.
    rewrite (nth_error_nth' l d) by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ i)) by (rewrite length_map, length_seq; lia). symmetry. apply nth_error_None.
    rewrite length_firstn, length_skipn. lia.
Qed.

Lemma wspan_bound : forall P Sl L F, 0 <= P -> 0 <= Sl -> 0 <= L ->
  0 <= fst (wspanZ P Sl L F) /\ 0 <= snd (wspanZ P Sl L F) /\ fst (wspanZ P Sl L F) + snd (wspanZ P Sl L F) <= P + L + Sl.
Proof. intros P Sl L [B0 [| | |] rc | rc | d | ] HP HS HL; cbn [wspanZ fst snd]; lia. Qed.
Lemma uE_laddc2 : forall E l c, 0 <= c -> uE E l + c < two64 -> uE E (laddc l c) = uE E l + c.
Proof. intros E l c Hc H. unfold uE. rewrite lden_laddc. apply u_small64. pose proof (uE_range E l). unfold uE in *. lia. Qed.
Lemma wspanL_sound : forall E P Sl lj F, 0 <= P < 2 ^ 20 -> 0 <= Sl < 2 ^ 20 -> uE E lj < 2 ^ 62 ->
  uE E (fst (wspanL P Sl lj F)) = fst (wspanZ P Sl (uE E lj) F) /\ uE E (snd (wspanL P Sl lj F)) = snd (wspanZ P Sl (uE E lj) F).
Proof.
  intros E P Sl lj F HP HS HL. pose proof (uE_range E lj) as RL.
  assert (C : forall c, 0 <= c < 2 ^ 62 -> uE E (lconst c) = c) by (intros c Hc; unfold uE; rewrite lden_lconst; apply u_small64; unfold two64; lia).
  assert (A : forall c, 0 <= c < 2 ^ 21 -> uE E (laddc lj c) = uE E lj + c) by (intros c Hc; apply uE_laddc2; unfold two64 in *; lia).
  destruct F as [B0 [| | |] rc | rc | d | ]; cbn [wspanL wspanZ fst snd]; split;
    first [rewrite C by lia; reflexivity | rewrite A by lia; lia | reflexivity | rewrite C by lia; lia].
Qed.

Section Iov.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Variable img : tree Z.
Hypothesis Himg : img_ok segs img.
Variable sarg : nat -> list byte.

#[using="sarg"] Lemma rd1_full_rdn' : forall m X n (f : nat -> byte), 0 <= X -> X + Z.of_nat n <= two64 ->
  (forall i, (i < n)%nat -> rd1 segs m (Z_to_bv 64 (X + Z.of_nat i)) = Some (f i)) ->
  rdn segs m (Z_to_bv 64 X) n = Some (List.map f (seq 0 n)).
Proof. LiaFast.lf_pins (fun (sarg : LiaFast.U) => LiaFast.u0).
  intros m X n f HX Hn Hall.
  destruct (rdn_from segs m n X HX Hn) as (bs & Hbs & Hlen & Hnth).
  { intros i Hi. rewrite <- (Z2Nat.id i) by lia. rewrite (Hall (Z.to_nat i) ltac:(lia)). discriminate. }
  rewrite Hbs. f_equal. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
  - rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n) as [_|Hc]; [|lia]. cbn [option_map]. rewrite Nat.add_0_l.
    destruct (nth_error bs i) as [b|] eqn:Hb.
    + pose proof (Hnth i b Hb) as X1. rewrite (Hall i Hi) in X1. congruence.
    + apply nth_error_None in Hb. lia.
  - rewrite (proj2 (nth_error_None bs i)) by lia. symmetry. apply nth_error_None. rewrite length_map, length_seq. lia.
Qed.

#[using="Himg"] Theorem iov_src_sound0 : forall E S M ms model recs pre suf j lj b l off0 F,
  DEN segs LIMIT model0 mem0 E S M ms model -> Forall (sbytes_ok sarg E mem0) recs ->
  uE E lj = Z.of_nat (length (sarg j)) -> snd (irange (s_facts S) lj) < 2 ^ 62 ->
  Z.of_nat (length pre) < 2 ^ 20 -> Z.of_nat (length suf) < 2 ^ 20 ->
  wsrc_ok img S M recs pre suf j lj F = true ->
  iov_src_ok0 (s_facts S) recs (Z.of_nat (length pre)) (Z.of_nat (length suf)) lj b l off0 F = true ->
  uE E off0 + uE E l <= Z.of_nat (length (msgb sarg pre suf j)) /\ uE E l < 2 ^ 40 /\ uE E b + uE E l <= TASK_SIZE /\
  rdn segs (mrestrict (Hof E M model) (ms_mem ms)) (lden E b) (Z.to_nat (uE E l)) =
    Some (firstn (Z.to_nat (uE E l)) (skipn (Z.to_nat (uE E off0)) (msgb sarg pre suf j))).
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros E S M ms model recs pre suf j lj b l off0 F Hd Hrec HLj Hlhi HP HS Hws Hok.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  set (P := Z.of_nat (length pre)) in *. set (Sl := Z.of_nat (length suf)) in *.
  pose proof (irange_sound E (s_facts S) lj HF) as Rl. fold (uE E lj) in Rl.
  destruct (wspanL_sound E P Sl lj F ltac:(lia) ltac:(lia) ltac:(lia)) as [Ho HT].
  destruct (wspan_bound P Sl (uE E lj) F ltac:(lia) ltac:(lia) ltac:(pose proof (uE_range E lj); lia)) as (Bo & BT & BoT).
  unfold iov_src_ok0 in Hok.
  destruct (wspanL P Sl lj F) as [o T] eqn:Hsp. cbn [fst snd] in Ho, HT.
  set (oZ := fst (wspanZ P Sl (uE E lj) F)) in *. set (TZ := snd (wspanZ P Sl (uE E lj) F)) in *.
  destruct (irange_d (s_facts S) (lsub off0 o)) as [lo1 hi1] eqn:Hr1.
  destruct (irange_d (s_facts S) (lsub (ladd o T) off0)) as [lo2 hi2] eqn:Hr2.
  repeat match type of Hok with ((_ && _)%bool = true) => apply andb_prop in Hok as [Hok ?Hq] end.
  apply lin_eqb_eq in Hok.
  repeat match goal with
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx
         | Hx : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx
         end.
  match goal with Hx : l = lsub (ladd o T) off0 |- _ => rename Hx into Hl end.
  rename Hok into Hb.
  match goal with Hx : (Z.leb (snd (irange (s_facts S) (wbase recs F)) + snd (irange (s_facts S) T)) TASK_SIZE || _)%bool = true |- _ => rename Hx into Hbd end.
  pose proof (irange_d_sound E (s_facts S) (lsub off0 o) lo1 hi1 HF Hr1 ltac:(lia)) as R1.
  pose proof (irange_d_sound E (s_facts S) (lsub (ladd o T) off0) lo2 hi2 HF Hr2 ltac:(lia)) as R2.
  pose proof (irange_sound E (s_facts S) (wbase recs F) HF) as RB. fold (uE E (wbase recs F)) in RB.
  pose proof (irange_sound E (s_facts S) T HF) as RT. fold (uE E T) in RT.
  pose proof (uE_range E off0) as Roff. pose proof (uE_range E (wbase recs F)) as RBa.
  assert (HbdZ : uE E (wbase recs F) + uE E T <= TASK_SIZE).
  { apply orb_prop in Hbd as [Hbd|Hbd]; [apply Z.leb_le in Hbd; lia|].
    apply andb_prop in Hbd as [Hbd Hb3]. apply andb_prop in Hbd as [Hb1 Hb2]. apply Z.ltb_lt in Hb1, Hb2. apply Z.leb_le in Hb3.
    pose proof (irange_sound E (s_facts S) (ladd (wbase recs F) T) HF) as RS. fold (uE E (ladd (wbase recs F) T)) in RS.
    assert (Hs : uE E (ladd (wbase recs F) T) = uE E (wbase recs F) + uE E T).
    { unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E (wbase recs F)) (uE E T). unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64. lia. }
    lia. }
  clear Hbd.
  assert (HLm : Z.of_nat (length (msgb sarg pre suf j)) = P + uE E lj + Sl) by (rewrite length_msgb, HLj; unfold P, Sl; lia).
  (* [comment removed for export] *)
  destruct (small_diff E off0 o lo1 hi1 R1) as [[Hl1 He1]|[Hl1 He1]]; [|exfalso; unfold two64 in *; lia].
  rewrite Ho in Hl1, He1.
  assert (HoT : uE E (ladd o T) = oZ + TZ).
  { unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E o) (uE E T). rewrite Ho, HT. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
  destruct (small_diff E (ladd o T) off0 lo2 hi2 R2) as [[Hl2 He2]|[Hl2 He2]]; rewrite HoT in Hl2, He2; [|exfalso; unfold two64 in *; lia].
  set (x0 := uE E off0 - oZ) in *.
  assert (HuL : uE E l = TZ - x0) by (rewrite Hl; unfold x0; lia).
  assert (HuB : uE E b = uE E (wbase recs F) + x0).
  { rewrite Hb. unfold uE at 1. rewrite lden_ladd, bv_add_unsigned. fold (uE E (wbase recs F)) (uE E (lsub off0 o)). rewrite <- He1.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold x0, TASK_SIZE, two64 in *. lia. }
  refine (conj _ (conj _ (conj _ _))).
  - rewrite HuL, HLm. unfold x0. lia.
  - rewrite HuL. unfold x0. lia.
  - rewrite HuB, HuL. unfold x0, TASK_SIZE in *. lia.
  - rewrite <- (Z_to_bv_bv_unsigned _ (lden E b)). fold (uE E b).
    rewrite (rd1_full_rdn' _ (uE E b) (Z.to_nat (uE E l)) (fun i => nth (Z.to_nat (uE E off0) + i) (msgb sarg pre suf j) (Z_to_bv 8 0))).
    + f_equal. apply map_nth_firstn_skipn. apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, !Z2Nat.id by lia. rewrite HLm, HuL. unfold x0. lia.
    + pose proof (uE_range E b). lia.
    + rewrite Z2Nat.id by lia. rewrite HuB, HuL. unfold x0, TASK_SIZE, two64 in *. lia.
    + intros i Hi. rewrite HuB. replace (uE E (wbase recs F) + x0 + Z.of_nat i) with (uE E (wbase recs F) + (x0 + Z.of_nat i)) by lia.
      rewrite (wsrc_sound segs LIMIT model0 mem0 img Himg sarg E S M ms model recs pre suf j lj F Hd Hrec HLj Hlhi Hws (x0 + Z.of_nat i)).
      * fold P Sl. fold oZ. f_equal. f_equal. unfold x0. lia.
      * fold P Sl. fold TZ. rewrite HuL in Hi. unfold x0 in *. lia.
Qed.

#[using="Himg"] Theorem iov_src_sound : forall E S M ms model recs pre suf j lj b l off0 F,
  DEN segs LIMIT model0 mem0 E S M ms model -> Forall (sbytes_ok sarg E mem0) recs ->
  uE E lj = Z.of_nat (length (sarg j)) -> snd (irange (s_facts S) lj) < 2 ^ 62 ->
  Z.of_nat (length pre) < 2 ^ 20 -> Z.of_nat (length suf) < 2 ^ 20 ->
  wsrc_ok img S M recs pre suf j lj F = true ->
  iov_src_ok (s_facts S) recs (Z.of_nat (length pre)) (Z.of_nat (length suf)) lj b l off0 F = true ->
  uE E off0 + uE E l <= Z.of_nat (length (msgb sarg pre suf j)) /\ uE E l < 2 ^ 40 /\ uE E b + uE E l <= TASK_SIZE /\
  rdn segs (mrestrict (Hof E M model) (ms_mem ms)) (lden E b) (Z.to_nat (uE E l)) =
    Some (firstn (Z.to_nat (uE E l)) (skipn (Z.to_nat (uE E off0)) (msgb sarg pre suf j))).
Proof. LiaFast.lf_pins (fun (Himg : LiaFast.U) => LiaFast.u0).
  intros E S M ms model recs pre suf j lj b l off0 F Hd Hrec HLj Hlhi HP HS Hws Hok.
  destruct F as [B0 kd rc | rc | d | ];
    [exact (iov_src_sound0 E S M ms model recs pre suf j lj b l off0 _ Hd Hrec HLj Hlhi HP HS Hws Hok) ..|].
  (* [comment removed for export] *)
  cbn [iov_src_ok] in Hok. apply andb_prop in Hok as [Hok Hb]. apply andb_prop in Hok as [Hl Ho].
  apply lin_eqb_eq in Hl, Ho. apply Z.leb_le in Hb. subst l off0.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (irange_sound E (s_facts S) lj HF) as Rl. fold (uE E lj) in Rl.
  pose proof (irange_sound E (s_facts S) b HF) as Rb. fold (uE E b) in Rb.
  assert (HL0 : uE E (lconst 0) = 0) by (unfold uE; rewrite lden_lconst; reflexivity).
  assert (HO : uE E (laddc lj (Z.of_nat (length pre) + Z.of_nat (length suf))) = uE E lj + (Z.of_nat (length pre) + Z.of_nat (length suf)))
    by (apply uE_laddc2; unfold two64; lia).
  rewrite HL0. refine (conj _ (conj _ (conj _ _))).
  - rewrite HO, length_msgb, HLj. lia.
  - lia.
  - lia.
  - reflexivity.
Qed.
End Iov.
