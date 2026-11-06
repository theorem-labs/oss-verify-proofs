(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg AHandoffLib MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AMainEntry.MainFactsAsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AEntryLib AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_kitL RT_init1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_init2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_init2.RT_initK.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_init2.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pdisj_has (l : list pfact) (a1 : zexp) (n1 : Z) (a2 : zexp) (n2 : Z) : bool :=
  existsb (fun f => match f with
                    | PDisj b1 k1 b2 k2 => (zexp_eqb b1 a1 && (k1 =? n1) && zexp_eqb b2 a2 && (k2 =? n2))
                                           || (zexp_eqb b1 a2 && (k1 =? n2) && zexp_eqb b2 a1 && (k2 =? n1))
                    | _ => false end) l.
Lemma pdisj_has_sound : forall V l a1 n1 a2 n2, Forall (pfact_ok V) l -> pdisj_has l a1 n1 a2 n2 = true ->
  zv V a1 + n1 <= zv V a2 \/ zv V a2 + n2 <= zv V a1.
Proof.
  intros V l a1 n1 a2 n2 HF H. unfold pdisj_has in H. apply existsb_exists in H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as K. destruct f as [| |b1 k1 b2 k2|]; try discriminate. cbn [pfact_ok] in K.
  apply orb_prop in Hf as [Hf|Hf]; repeat (apply andb_prop in Hf as [Hf ?]);
    repeat match goal with H : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in H | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end;
    subst; lia.
Qed.

(* [comment removed for export] *)
Lemma pvar_find : forall V l k lo hi, Forall (pfact_ok V) l ->
  existsb (fun f => match f with PVar n l0 h0 => Nat.eqb n k && (lo <=? l0) && (h0 <=? hi) | _ => false end) l = true -> lo <= V k <= hi.
Proof.
  intros V l k lo hi HF HE. apply existsb_exists in HE as (f & Hin & Hf). destruct f as [n l0 h0| | |]; try discriminate.
  apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst n.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as K. cbn [pfact_ok] in K. lia.
Qed.

Definition prange_has (l : list pfact) (e : zexp) (lo hi : Z) : bool :=
  existsb (fun f => match f with PRange e' lo' hi' => zexp_eqb e' e && (lo <=? lo') && (hi' <=? hi) | _ => false end) l.
Lemma prange_has_sound : forall V l e lo hi, Forall (pfact_ok V) l -> prange_has l e lo hi = true -> lo <= zv V e mod 2^64 <= hi.
Proof.
  intros V l e lo hi HF H. unfold prange_has in H. apply existsb_exists in H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as K. destruct f as [|e' lo' hi'| |]; try discriminate. cbn [pfact_ok] in K.
  apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2]. apply zexp_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  subst e'. unfold two64 in K. lia.
Qed.

(* [comment removed for export] *)
Definition obj : Type := (zexp * Z)%type.
Definition oden (V : nat -> Z) (o : obj) : Z * Z := (zv V (fst o), zv V (fst o) + snd o).

Fixpoint pw_chk (l : list pfact) (os : list obj) : bool :=
  match os with
  | [] => true
  | o :: r => forallb (fun o' => pdisj_has l (fst o) (snd o) (fst o') (snd o')) r && pw_chk l r
  end.
Lemma pw_chk_sound : forall V l os, Forall (pfact_ok V) l -> pw_chk l os = true -> pwdj (map (oden V) os).
Proof.
  intros V l os HF. induction os as [|o r IH]; intros H; cbn [pw_chk map pwdj] in *; [exact I|].
  apply andb_prop in H as [H1 H2]. split; [| exact (IH H2)].
  apply Forall_forall. intros r' Hr'. apply in_map_iff in Hr' as (o' & <- & Ho').
  rewrite forallb_forall in H1. pose proof (pdisj_has_sound V l _ _ _ _ HF (H1 o' Ho')) as D. cbn [oden fst snd]. lia.
Qed.

(* [comment removed for export] *)
Definition clr_chk (l : list pfact) (lo n : Z) (os : list obj) : bool :=
  forallb (fun o => pdisj_has l (fst o) (snd o) (ZLit lo) n) os.
Lemma clr_chk_sound : forall V l lo n os o, Forall (pfact_ok V) l -> clr_chk l lo n os = true -> In o os ->
  zv V (fst o) + snd o <= lo \/ lo + n <= zv V (fst o).
Proof.
  intros V l lo n os o HF H Ho. unfold clr_chk in H. rewrite forallb_forall in H.
  exact (pdisj_has_sound V l _ _ _ _ HF (H o Ho)).
Qed.

(* [comment removed for export] *)
Definition ledger_has (l : list lentry) (b : zexp) (n : Z) : bool :=
  existsb (fun e => match e with LMap b' n' _ => zexp_eqb b' b && (n' =? n) | _ => false end) l.
Lemma ledger_has_In : forall V l maps b n, ledger_den V l maps -> ledger_has l b n = true -> In (wa (zv V b), wa n) maps.
Proof.
  intros V l maps b n HD H. unfold ledger_has in H. apply existsb_exists in H as (e & Hin & He).
  destruct e as [b' n' k|]; [|discriminate]. apply andb_prop in He as [H1 H2]. apply zexp_eqb_eq in H1. apply Z.eqb_eq in H2. subst b' n'.
  exact (ledger_den_In V l maps b n k HD Hin).
Qed.
Lemma ledger_len : forall V l maps, ledger_den V l maps -> (length maps <= length l)%nat.
Proof.
  intros V l. induction l as [|e l IH]; intros maps HD; cbn [ledger_den] in HD.
  - subst maps. cbn. lia.
  - destruct e as [b n k|n].
    + destruct HD as (maps' & -> & HD). cbn [length]. pose proof (IH _ HD). lia.
    + destruct HD as [HD|(iv & maps' & -> & _ & HD)]; [pose proof (IH _ HD); cbn [length]; lia| cbn [length]; pose proof (IH _ HD); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OBJK : list (nat * Z) :=
  [(208%nat, 137439023104); (226%nat, 8388608);
   (471%nat, 4096); (377%nat, 11571200); (310%nat, 4096); (245%nat, 4096); (228%nat, 65536); (227%nat, 4096); (207%nat, 3727360); (78%nat, 65536);
   (453%nat, 1048576); (454%nat, 8388608)].
Definition kobj (e : nat * Z) : obj := (ZMul (ZLit 4096) (ZV (fst e)), snd e).
Definition OBJS : list obj := map kobj OBJK.

Definition objk_chk (lp : list pfact) (ll : list lentry) : bool :=
  forallb (fun e => existsb (fun f => match f with PVar n lo hi => Nat.eqb n (fst e) && (1 <=? lo) && (hi <=? 2^35) | _ => false end) lp
                    && (0 <? snd e) && (snd e <? 2^40) && ledger_has ll (fst (kobj e)) (snd e)) OBJK
  && pw_chk lp OBJS
  && clr_chk lp 2147446784 17592186048512 OBJS.         (* [comment removed for export] *)
Lemma objk_ok : objk_chk asan_pure_facts asan_ledger = true.
Proof. vm_compute. reflexivity. Qed.

Section PURE.
Context {ACEIL : Ceil}.
Variables (w : bool) (V : nat -> Z) (sp0 : word) (fs : Fs.Fs) (mo : Model).
Let usp := bv_unsigned sp0.
Hypothesis HU : usp = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.
Hypothesis HPW : Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w).
Hypothesis HM : amodel V sp0 fs mo.
Hypothesis HC : alloc_ceiling = usp - 8388608.
Let HP : Forall (pfact_ok V) asan_pure_facts := proj1 (proj1 (Forall_app _ _ _) HPW).

Lemma rt_ranges_main : forall h, rt_ranges (st_main h V usp) = map (oden V) OBJS.
Proof. intros h. reflexivity. Qed.

Lemma obj_facts : forall e, In e OBJK ->
  let lo := 4096 * V (fst e) in let hi := lo + snd e in
  In (wz lo, wz (snd e)) (vm_maps (m_vmmaps mo))
  /\ oclr lo hi /\ lo < hi /\ hi <= alloc_ceiling /\ lo mod 4096 = 0.
Proof.
  intros e He lo hi. pose proof objk_ok as C. unfold objk_chk in C.
  apply andb_prop in C as [C C4]. apply andb_prop in C as [C1 C2].
  rewrite forallb_forall in C1. specialize (C1 e He).
  apply andb_prop in C1 as [C1 L]. apply andb_prop in C1 as [C1 N2]. apply andb_prop in C1 as [PV N1].
  apply Z.ltb_lt in N1. apply Z.ltb_lt in N2.
  pose proof (pvar_find V _ (fst e) 1 (2^35) HP PV) as RV.
  assert (Ho : In (kobj e) OBJS) by (apply in_map; exact He).
  pose proof (clr_chk_sound V _ _ _ _ _ HP C4 Ho) as HS.
  cbn [kobj fst snd zv] in HS. fold lo in HS.
  pose proof (ledger_has_In V _ _ _ _ (am_maps _ _ _ _ HM) L) as HIn. cbn [kobj fst snd zv] in HIn. fold lo in HIn.
  pose proof (proj1 (Forall_forall _ _) (am_bounds _ _ _ _ HM) _ HIn) as (_ & _ & _ & _ & HI & HB). cbn [fst snd] in HI, HB.
  rewrite !wa_unsigned in HI, HB by (unfold lo; lia). fold usp in HB. unfold AM_IMG_LO, AM_IMG_HI in HI.
  split; [exact HIn|]. split; [| split; [unfold hi; lia| split; [unfold hi; lia| unfold lo; rewrite Z.mul_comm; apply Z_mod_mult]]].
  split; [unfold sclr, KLOWSHADOW_BEG, KHIGHMEM_BEG| unfold iclr, AIMG_LO, AIMG_HI]; unfold hi in *; lia.
Qed.

Lemma usp_facts : 0x7fff80000000 <= usp /\ usp + 192 <= 2^47 /\ usp mod 16 = 0.
Proof.
  destruct (am_usp _ _ _ _ HM) as (U1 & U2 & U3). fold usp in U1, U2, U3. split; [exact U1|]. split; [| exact U3].
  pose proof (prange_has_sound V _ (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))
                140735340871680 140737488355136 HP ltac:(vm_compute; reflexivity)) as R. cbn [zv] in R.
  replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat)) with usp in R by lia.
  rewrite Z.mod_small in R by lia. lia.
Qed.

Theorem IP_main : init_pure (hw w) V usp.
Proof.
  pose proof (pvar_find V _ 209%nat 0 15 HP ltac:(vm_compute; reflexivity)) as R209.
  pose proof (pvar_find V _ 6%nat 0 255 HP ltac:(vm_compute; reflexivity)) as R6.
  pose proof (pvar_find V _ 344%nat 0 1 HP ltac:(vm_compute; reflexivity)) as R344.
  constructor.
  - destruct w; [left| right]; reflexivity.
  - exact usp_facts.
  - exact R209.
  - pose proof (prange_has_sound V _ (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0 HP
                  ltac:(vm_compute; reflexivity)) as R. cbn [zv] in R.
    change 65535 with (Z.ones 16) in R. rewrite Z.land_ones in R by lia. change (2 ^ 16) with 65536 in R.
    pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as MB.
    set (x := -4096 * V 209%nat + (4096 * V 208%nat) mod 65536) in *.
    destruct (Z_lt_le_dec x 0) as [Hn|Hp].
    + exfalso. replace x with ((x + 2^64) + (-1) * 2^64) in R by lia. rewrite Z.mod_add in R by lia. rewrite Z.mod_small in R by lia. lia.
    + rewrite Z.mod_small in R by lia. lia.
  - intros r Hr. rewrite rt_ranges_main in Hr. unfold OBJS in Hr. rewrite map_map in Hr. apply in_map_iff in Hr as (e & <- & He).
    destruct (obj_facts e He) as (_ & A & B & C & D). cbn [oden kobj fst snd zv]. exact (conj A (conj B (conj C D))).
  - rewrite rt_ranges_main. apply (pw_chk_sound V asan_pure_facts OBJS HP).
    pose proof objk_ok as C. unfold objk_chk in C. apply andb_prop in C as [C _]. apply andb_prop in C as [_ C]. exact C.
  - exact HU.
  - pose proof (prange_has_sound V _ (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095 HP
                  ltac:(vm_compute; reflexivity)) as R. cbn [zv] in R.
    set (x := 16 * V 6%nat + -4096 * V 344%nat + 3935) in *.
    destruct (Z_lt_le_dec x 0) as [Hn|Hp].
    + exfalso. replace x with ((x + 2^64) + (-1) * 2^64) in R by lia. rewrite Z.mod_add in R by lia. rewrite Z.mod_small in R by lia. lia.
    + rewrite Z.mod_small in R by lia. lia.
Qed.
End PURE.
