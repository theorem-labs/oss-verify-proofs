(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanPlanSound AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AH0Base () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.pv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_lla"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_ictx"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_prim"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_secv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_thr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_treg"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_tvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dtls"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_tmpv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_fstk"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_mus1"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_mus2"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dnodes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dstore"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_gvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_divec"; "Corelib.Init.Datatypes.nil"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.In"; "PAGEVARS"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.nt"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.NDisj"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.AOff"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WLit"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WVar"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CNSTS"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "PG"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.ALit"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s1"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s2"; "Objects.W_STKPG"; "Stdlib.ZArith.BinInt.Z.sub"; "Objects.STKPG"].


Local Notation u64_range := ABoot.PropExec.u64_range.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uv (p : me_params) (v : pv) : Z := bv_unsigned (pget p v).

Lemma uv_range : forall p v, 0 <= uv p v < 2 ^ 64.
Proof. intros p v. unfold uv. apply u64_range. Qed.

(* [comment removed for export] *)
Fixpoint zev (p : me_params) (t : wt) : Z :=
  match t with
  | WLit z => z
  | WVar v => uv p v
  | WAlu ALU_ADD a b => zev p a + zev p b
  | WAlu ALU_SUB a b => zev p a - zev p b
  | WMd M_MUL a b => zev p a * zev p b
  | WAlu ALU_AND a b => Z.land (zev p a mod 2 ^ 64) (zev p b mod 2 ^ 64)
  | WAlu ALU_SRL a b => (zev p a mod 2 ^ 64) / 2 ^ ((zev p b mod 2 ^ 64) mod 64)
  | WAlu ALU_SLTU a b => if (zev p a mod 2 ^ 64) <? (zev p b mod 2 ^ 64) then 1 else 0
  | _ => bv_unsigned (winst p t)
  end.

Lemma zmod64_range : forall z, 0 <= z mod 2 ^ 64 < 2 ^ 64.
Proof. intros z. apply Z.mod_pos_bound. lia. Qed.

Theorem zev_sound : forall p t, bv_unsigned (winst p t) = zev p t mod 2 ^ 64.
Proof.
  assert (TRIV : forall w : word, bv_unsigned w = bv_unsigned w mod 2 ^ 64).
  { intros w. symmetry. apply Z.mod_small. apply u64_range. }
  intros p t. induction t as [z | v | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | op a IHa b IHb | sx lo n a IHa].
  - (* [comment removed for export] *) cbn [winst zev]. rewrite Z_to_bv_unsigned, ABoot.PropExec.bv_wrap64_mod. reflexivity.
  - (* [comment removed for export] *) cbn [winst zev]. unfold uv. apply TRIV.
  - (* [comment removed for export] *) destruct op; cbn [winst zev]; try apply TRIV.
    + rewrite u_add64, IHa, IHb. rewrite <- Z.add_mod by lia. reflexivity.
    + rewrite u_sub64, IHa, IHb. rewrite <- Zminus_mod. reflexivity.
    + rewrite u_sltu64, IHa, IHb. destruct (_ <? _); reflexivity.
    + rewrite u_srl64, IHa, IHb. symmetry. apply Z.mod_small.
      pose proof (zmod64_range (zev p a)) as Ra.
      assert (Hp : 0 < 2 ^ ((zev p b mod 2 ^ 64) mod 64)) by (apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]).
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
    + rewrite u_and64, IHa, IHb. symmetry. apply Z.mod_small.
      pose proof (zmod64_range (zev p a)). pose proof (zmod64_range (zev p b)). apply ABoot.PropExec.Z_land_range; lia.
  - (* [comment removed for export] *) cbn [winst zev]. apply TRIV.
  - (* [comment removed for export] *) destruct op; cbn [winst zev]; try apply TRIV.
    rewrite u_mul64, IHa, IHb. rewrite <- Z.mul_mod by lia. reflexivity.
  - cbn [winst zev]. apply TRIV.
  - cbn [winst zev]. apply TRIV.
Qed.

(* [comment removed for export] *)
Lemma zev_exact : forall p t, 0 <= zev p t < 2 ^ 64 -> bv_unsigned (winst p t) = zev p t.
Proof. intros p t H. rewrite zev_sound. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Lemma azinst_lit : forall p z, azinst p (ALit z) = z.
Proof. reflexivity. Qed.
Lemma azinst_off : forall p b off, 0 <= zev p b < 2 ^ 64 -> azinst p (AOff b off) = zev p b + off.
Proof. intros p b off H. cbn [azinst]. rewrite (zev_exact p b H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cnsts.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).

  #[using="HCN"] Lemma cnst_nth : forall i c, nth_error CNSTS i = Some c -> cnst_ok (ninst p c).
  Proof.
    intros i c H. unfold me_cnsts in HCN. apply (proj1 (Forall_forall _ _) HCN). apply in_map. eapply nth_error_In. exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="HCN"] Lemma cnst_range : forall i lo t hi, nth_error CNSTS i = Some (NRange lo t hi) ->
    lo <= zev p t mod 2 ^ 64 <= hi.
  Proof. intros i lo t hi H. pose proof (cnst_nth i _ H) as C. cbn [ninst cnst_ok] in C. rewrite zev_sound in C. exact C. Qed.

  (* [comment removed for export] *)
  End Cnsts.

(* [comment removed for export] *)
Definition nt_eqb_range (v : pv) (c : nt) : bool :=
  match c with NRange _ (WVar v') _ => pv_beq v v' | _ => false end.
Fixpoint find_index {X} (f : X -> bool) (l : list X) (i : nat) : option nat :=
  match l with [] => None | x :: l' => if f x then Some i else find_index f l' (S i) end.
Lemma find_index_sound {X} : forall (f : X -> bool) l i k, find_index f l i = Some k ->
  exists x, nth_error l (k - i) = Some x /\ f x = true /\ (i <= k)%nat.
Proof.
  intros f l. induction l as [|x l IH]; intros i k H; cbn [find_index] in H; [discriminate H|].
  destruct (f x) eqn:Fx.
  - injection H as <-. exists x. rewrite Nat.sub_diag. cbn. auto.
  - ddestruct (IH (S i) k H) as (y & Hy & Fy & Le). exists y. replace (k - i)%nat with (S (k - S i)) by lia. cbn [nth_error].
    split; [exact Hy|]. split; [exact Fy | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PG (p : me_params) (v : pv) : Z := 4096 * uv p v.

Section Pages.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).

  (* [comment removed for export] *)
  #[using="HCN"] Lemma var_range : forall v lo hi i,
    nth_error CNSTS i = Some (NRange lo (WVar v) hi) -> lo <= uv p v <= hi.
  Proof.
    intros v lo hi i H. pose proof (cnst_range p HCN i lo (WVar v) hi H) as C. cbn [zev] in C.
    rewrite Z.mod_small in C by apply uv_range. exact C.
  Qed.

  (* [comment removed for export] *)
  Definition PAGEVARS : list pv := ltac2:(CDefT.buildp (gd_tbl_AH0Base ()) "(0.$1.$2.(0.$1.$3.(0.$1.$4.(0.$1.$5.(0.$1.$6.(0.$1.$7.(0.$1.$8.(0.$1.$9.(0.$1.$:.(0.$1.$;.(0.$1.$<.(0.$1.$=.(0.$1.$>.(0.$1.$?.(0.$1.$10.(0.$1.$11.(12.$1.)))))))))))))))))")
(* [comment removed for export] *).
  Definition pagevar_ok (v : pv) : bool :=
    match find_index (nt_eqb_range v) CNSTS 0 with
    | Some i => match nth_error CNSTS i with
                | Some (NRange lo (WVar _) hi) => ((1 <=? lo) && (hi <=? 0x7fffff7ff))%bool
                | _ => false
                end
    | None => false
    end.
  #[using="Type"] Lemma pagevars_ok : forallb pagevar_ok PAGEVARS = true.
  Proof. vm_compute. reflexivity. Qed.

  #[using="HCN"] Lemma pagevar_range : forall v, In v PAGEVARS -> 1 <= uv p v <= 0x7fffff7ff.
  Proof.
    intros v Hv. pose proof (proj1 (forallb_forall _ _) pagevars_ok v Hv) as H. unfold pagevar_ok in H.
    destruct (find_index (nt_eqb_range v) CNSTS 0) as [i|] eqn:Fi; [|discriminate H].
    destruct (find_index_sound _ _ _ _ Fi) as (c & Hc & Fc & _). rewrite Nat.sub_0_r in Hc. rewrite Hc in H.
    destruct c as [lo [z|v'|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?] hi| | ]; try discriminate H.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    cbn [nt_eqb_range] in Fc. apply pv_beq_eq in Fc. subst v'.
    pose proof (var_range v lo hi i Hc). lia.
  Qed.

  #[using="HCN"] Lemma PG_range : forall v, In v PAGEVARS -> 4096 <= PG p v <= 0x7fffff7ff000 /\ PG p v mod 4096 = 0.
  Proof. intros v Hv. pose proof (pagevar_range v Hv). unfold PG. split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

  (* [comment removed for export] *)
    #[using="HCN"] Lemma u_page : forall v, In v PAGEVARS -> bv_unsigned (winst p (WMd M_MUL (WLit 0x1000) (WVar v))) = PG p v.
  Proof. intros v Hv. rewrite zev_exact; [reflexivity|]. cbn [zev]. pose proof (pagevar_range v Hv). unfold uv in *. lia. Qed.
  #[using="HCN"] Lemma Page_eq : forall v, In v PAGEVARS -> bv_unsigned (Page p v) = PG p v.
  Proof. intros v Hv. unfold Page. apply u_page. exact Hv. Qed.
End Pages.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nt_eqb (a b : nt) : bool :=
  match a, b with
  | NRange lo v hi, NRange lo' v' hi' => (Z.eqb lo lo' && wt_eqb v v' && Z.eqb hi hi')%bool
  | NDisj a1 n1 b1 m1, NDisj a2 n2 b2 m2 => (at_eqb a1 a2 && wt_eqb n1 n2 && at_eqb b1 b2 && wt_eqb m1 m2)%bool
  | NAlign v m, NAlign v' m' => (wt_eqb v v' && Z.eqb m m')%bool
  | _, _ => false
  end.
Lemma nt_eqb_eq : forall a b, nt_eqb a b = true -> a = b.
Proof.
  intros [lo v hi|a1 n1 b1 m1|v m] [lo' v' hi'|a2 n2 b2 m2|v' m'] H; cbn [nt_eqb] in H; try discriminate H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : wt_eqb _ _ = true |- _ => apply wt_eqb_eq in H
      | H : at_eqb _ _ = true |- _ => apply at_eqb_eq in H
      end; subst; reflexivity.
Qed.
Lemma In_CNSTS : forall c, existsb (nt_eqb c) CNSTS = true -> In c CNSTS.
Proof.
  intros c H. apply existsb_exists in H as (c' & Hin & Heq). apply nt_eqb_eq in Heq. subst c'. exact Hin.
Qed.

Section Objects.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).

  #[using="HCN"] Lemma me_cnst : forall c, In c CNSTS -> cnst_ok (ninst p c).
  Proof. intros c Hc. unfold me_cnsts in HCN. exact (proj1 (Forall_forall _ _) HCN (ninst p c) (in_map _ _ _ Hc)). Qed.

  (* [comment removed for export] *)
  #[using="HCN"] Lemma pages_apart : ltac2:(CDefT.buildp (gd_tbl_AH0Base ()) "Pa,$1.Pla,$13.Pb,$1.Plb,$13.P,(14.$1.R4.$15.)P,(14.$1.R3.$15.)P,(16.(17.=R5.)(18.R5.(19.+2.+40.)))P,(16.(17.=R4.)(18.R4.(19.+2.+40.)))P,(14.$1:.(1;.(1<.(1=.$1>.(1?.+1000.)(20.R8.))=)(1?.R7.)(1<.(1=.$1>.(1?.+1000.)(20.R6.))=)(1?.R5.))$21.)(22.(17.(23.(24.Vp,R9.)R8.)(24.Vp,R7.))(17.(23.(24.Vp,R7.)R6.)(24.Vp,R9.)))")
(* [comment removed for export] *).
  Proof.
    intros a la b lb Ha Hb Hla Hlb Hin. pose proof (me_cnst _ Hin) as C. cbn [ninst cnst_ok] in C.
    rewrite !(azinst_off p) in C by (cbn [zev]; pose proof (pagevar_range p HCN _ Ha); pose proof (pagevar_range p HCN _ Hb); unfold uv in *; lia).
    cbn [zev winst] in C. rewrite !u_lit64a in C.
    pose proof (pagevar_range p HCN _ Ha). pose proof (pagevar_range p HCN _ Hb).
    unfold PG, uv in *. rewrite !Z.mod_small in C by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HCN"] Lemma page_hull_apart : ltac2:(CDefT.buildp (gd_tbl_AH0Base ()) "Pv,$1.Plen,$13.P,(14.$1.R2.$15.)P,(16.(17.=R2.)(18.R2.(19.+2.+40.)))P,(14.$1:.(1;.(25.+10000.)(1?.+64?000.)(1<.(1=.$1>.(1?.+1000.)(20.R4.))=)(1?.R3.))$21.)(22.(17.(23.(24.Vp,R5.)R4.)+10000.)(17.+65?000.(24.Vp,R5.)))")
(* [comment removed for export] *).
  Proof.
    intros v len Hv Hlen Hin. pose proof (me_cnst _ Hin) as C. cbn [ninst cnst_ok] in C.
    pose proof (pagevar_range p HCN _ Hv).
    rewrite azinst_lit, (azinst_off p) in C by (cbn [zev]; unfold uv in *; lia).
    cbn [zev winst] in C. rewrite !u_lit64a in C. unfold PG, uv in *. rewrite !Z.mod_small in C by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HCN"] Lemma page_band_apart : ltac2:(CDefT.buildp (gd_tbl_AH0Base ()) "Pv,$1.Plen,$13.P,(14.$1.R2.$15.)P,(16.(17.=R2.)(18.R2.(19.+2.+40.)))P,(14.$1:.(1;.(25.+7???7000.)(1?.+100000001000.)(1<.(1=.$1>.(1?.+1000.)(20.R4.))=)(1?.R3.))$21.)(22.(17.(23.(24.Vp,R5.)R4.)+7???7000.)(17.+10007???8000.(24.Vp,R5.)))")
(* [comment removed for export] *).
  Proof.
    intros v len Hv Hlen Hin. pose proof (me_cnst _ Hin) as C. cbn [ninst cnst_ok] in C.
    pose proof (pagevar_range p HCN _ Hv).
    rewrite azinst_lit, (azinst_off p) in C by (cbn [zev]; unfold uv in *; lia).
    cbn [zev winst] in C. rewrite !u_lit64a in C. unfold PG, uv in *. rewrite !Z.mod_small in C by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition STKPG : Z := 32768 * uv p v_s1 + 4096 * (uv p v_s2 / 256).
  Definition W_STKPG : wt := ltac2:(CDefT.buildp (gd_tbl_AH0Base ()) "(26.$27.(1=.$1>.(1?.+8000.)(20.$28.))(1=.$1>.(1?.+1000.)(26.$29.(20.$2:.)(1?.+8.))))")
(* [comment removed for export] *).
  Hypothesis Hs1 : uv p v_s1 <= 0xffffffff.
  Hypothesis Hs2 : uv p v_s2 <= 2047.
  #[using="Hs2"] Lemma zev_STKPG : zev p W_STKPG = STKPG.
  Proof.
    cbn [zev W_STKPG]. unfold STKPG. pose proof (uv_range p v_s1). pose proof (uv_range p v_s2).
    rewrite (Z.mod_small (uv p v_s2)) by lia. rewrite (Z.mod_small 8) by lia. change (2 ^ (8 mod 64)) with 256. reflexivity.
  Qed.
  #[using="HCN Hs1 Hs2"] Lemma page_stack_apart : ltac2:(CDefT.buildp (gd_tbl_AH0Base ()) "Pv,$1.Plen,$13.P,(14.$1.R2.$15.)P,(16.(17.=R2.)(18.R2.(19.+2.+40.)))P,(14.$1:.(1;.(1<.$2;.-800000.)(1?.+800000000000.)(1<.(1=.$1>.(1?.+1000.)(20.R4.))=)(1?.R3.))$21.)(17.(23.(24.Vp,R5.)R4.)(2<.$2=.+800000.))")
(* [comment removed for export] *).
  Proof.
    intros v len Hv Hlen Hin. pose proof (me_cnst _ Hin) as C. cbn [ninst cnst_ok] in C.
    pose proof (pagevar_range p HCN _ Hv).
    rewrite (azinst_off p W_STKPG) in C by (rewrite zev_STKPG; unfold STKPG; pose proof (uv_range p v_s2); pose proof (uv_range p v_s1); pose proof (Z.div_pos (uv p v_s2) 256); lia).
    rewrite (azinst_off p) in C by (cbn [zev]; unfold uv in *; lia).
    rewrite zev_STKPG in C. cbn [zev winst] in C. rewrite !u_lit64a in C. rewrite !Z.mod_small in C by lia.
    unfold PG, STKPG, uv in *. pose proof (uv_range p v_s2). pose proof (uv_range p v_s1). pose proof (Z.div_pos (uv p v_s2) 256). unfold uv in *. lia.
  Qed.
End Objects.
