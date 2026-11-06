(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk AgentLib AsanAcct BackingAlgebra AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanNodesMmLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB HS2Both B_MainFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require RunCeiling MState Mem Cells Step InitMem Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require AImages AImageFacts NodesA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require AsanConsts AsanSizeClass AsanState AsanLayout AsanKern AsanRep AsanRepFrame AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require B_base.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require BF_fakestack_rep BF_place B_policy5 B_slack5 B_bundle B_benv5.
From stdpp Require fin_maps gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pgv (E : env) (v : nat) : Z := 4096 * bv_unsigned (ev E v).
(* [comment removed for export] *)
Definition pgE (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).

(* [comment removed for export] *)
Definition rcase0 (hs : acs) : bool := Nat.eqb (length (kn hs)) (length (kn HS_s2_00)) || Nat.eqb (length (kn hs)) (length (kn HS_s2_10)).
Definition keys0_of (hs : acs) : list (list Z) := if rcase0 hs then [[0x3fbe4; 0x40f34]] else [[0x3fbe4]].
Definition frames0_of (hs : acs) : Z := if rcase0 hs then 3 else 2.

(* [comment removed for export] *)
Definition A_IMG : Z * Z := (0x10000, 0x5f3000).

(* [comment removed for export] *)
Definition reserved_of (E : env) : list (Z * Z) :=
  [ (pgv E 245, 4096); (pgv E 246, 65536); (pgv E 438, 11571200); (pgv E 515, 8388608); (pgv E 514, 1048576);
    (pgv E 244, 8388608); (pgv E 226, 0x2000011000); (pgv E 340, 4096); (pgv E 275, 4096); (pgv E 532, 4096);
    (pgv E 225, 3727360); (pgv E 95, 65536);
    (0x7fff7000, 268435456); (0x8fff7000, 2199023255552); (0x2008fff7000, 15392894357504); A_IMG ].

Definition aenv_of (hs : acs) (E : env) : AsanState.aenv :=
  {| AsanState.ae_ic := AsanConsts.both_ic;
     AsanState.ae_sp0 := bv_unsigned (edenot E e_sp0);
     AsanState.ae_tp := 0x5e1550;
     AsanState.ae_thread := pgv E 245;
     AsanState.ae_space_beg := pgv E 226 - pgv E 227 + 0x10000;
     AsanState.ae_resv_beg := pgv E 226;
     AsanState.ae_ptr_array := pgv E 244;
     AsanState.ae_depot_nodes := pgv E 514;
     AsanState.ae_store_blk := pgv E 515;
     AsanState.ae_keys0 := keys0_of hs;
     AsanState.ae_frames0 := frames0_of hs;
     AsanState.ae_reserved := reserved_of E;
     AsanState.ae_fs_beg := pgv E 438;
     AsanState.ae_fs_len := 11571200;
     AsanState.ae_iarena := pgv E 246;
     AsanState.ae_img := A_IMG |}.

Definition fsbase_of (E : env) : Z := pgv E 438.

(* [comment removed for export] *)
Definition plumb_of (E : env) : BF_fakestack_rep.fs_plumb :=
  BF_fakestack_rep.mkFsPlumb (pgv E 246) (pgv E 340) 0x5e1550 0x5e1c88 0x5e1d64.

(* [comment removed for export] *)
Definition l0_head (E : env) : list (word * word) :=
  [ (Z_to_bv 64 (pgv E 532), Z_to_bv 64 4096); (Z_to_bv 64 (pgv E 515), Z_to_bv 64 8388608); (Z_to_bv 64 (pgv E 514), Z_to_bv 64 1048576) ].
Definition l0_tail (E : env) : list (word * word) :=
  [ (Z_to_bv 64 (pgv E 438), Z_to_bv 64 11571200); (Z_to_bv 64 (pgv E 340), Z_to_bv 64 4096); (Z_to_bv 64 (pgv E 275), Z_to_bv 64 4096);
    (Z_to_bv 64 (pgv E 246), Z_to_bv 64 65536); (Z_to_bv 64 (pgv E 245), Z_to_bv 64 4096); (Z_to_bv 64 (pgv E 244), Z_to_bv 64 8388608);
    (Z_to_bv 64 (pgv E 226), Z_to_bv 64 0x2000011000); (Z_to_bv 64 (pgv E 225), Z_to_bv 64 3727360); (Z_to_bv 64 (pgv E 95), Z_to_bv 64 65536);
    (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 15392894357504); (Z_to_bv 64 0x8fff7000, Z_to_bv 64 2199023255552); (Z_to_bv 64 0x7fff7000, Z_to_bv 64 268435456) ].
Definition l0_of (E : env) : list (word * word) := l0_head E ++ l0_tail E.

(* [comment removed for export] *)
Definition A_EB0 : Z := 16515072.

(* [comment removed for export] *)
Ltac inlist := first [left; reflexivity | right; inlist].

Section MainInit.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable hw : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable uid : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.

  Variable E : env.
  Variable R : bvmap 5 word.
  Variable FULL : word -> option byte.
  Variable model : Model.
  Variable hs : acs.
  Hypothesis Hhs : HS_MAIN hs.
  Hypothesis HC : cs_ok BSEGS BOTH5 LIM SINV argH fs E hs R FULL model.

  #[local] Notation FACT := (B_MainFacts.fact_sound sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC).
  #[local] Notation MR := (Mr BOTH5 argH E hs model FULL).
  Let usp := bv_unsigned sp.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pgv_range : forall v lo hi, hs_fact (KRange (EVar v) lo hi) = true -> 4096 * lo <= pgv E v <= 4096 * hi.
  Proof. intros v lo hi HK. pose proof (FACT _ HK) as [H1 H2]. cbn [edenot] in H1, H2. unfold pgv. lia. Qed.

  (* [comment removed for export] *)
  Lemma disj_fact : forall b1 o1 n1 b2 o2 n2, hs_fact (KDisj (SA b1 o1) n1 (SA b2 o2) n2) = true ->
    uE E b1 + o1 + uE E n1 <= uE E b2 + o2 \/ uE E b2 + o2 + uE E n2 <= uE E b1 + o1.
  Proof. intros b1 o1 n1 b2 o2 n2 HK. pose proof (FACT _ HK) as HD. cbn [kentry_ok] in HD. unfold estart, elenZ, uE in *. cbn [a_base a_off] in HD. lia. Qed.

  (* [comment removed for export] *)
  Lemma u_pg : forall v, pgv E v < 2 ^ 64 -> uE E (pgE v) = pgv E v.
  Proof.
    intros v Hv. unfold uE, pgE. cbn [edenot]. rewrite u_mul64, u64_lit by lia. unfold pgv in *.
    pose proof (u64_range (ev E v)). apply Z.mod_small. lia.
  Qed.
  Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
  Proof. intros z Hz. unfold uE. cbn [edenot]. apply u64_lit. lia. Qed.
  Lemma edenot_pg : forall v, pgv E v < 2 ^ 64 -> edenot E (pgE v) = Z_to_bv 64 (pgv E v).
  Proof. intros v Hv. apply bv_eq. rewrite u64_lit by (unfold pgv in *; pose proof (u64_range (ev E v)); lia). exact (u_pg v Hv). Qed.
  Lemma u_pg_off : forall v z, 0 <= z -> pgv E v + z < 2 ^ 64 -> uE E (EAlu Instr.ALU_ADD (pgE v) (ELit z)) = pgv E v + z.
  Proof.
    intros v z Hz Hv. pose proof (u64_range (ev E v)) as Rv.
    assert (Hp : pgv E v < 2 ^ 64) by (unfold pgv in *; lia). pose proof (u_pg v Hp) as U. unfold uE in *. cbn [edenot] in *.
    unfold pgv in *. rewrite u_add64. rewrite U, u64_lit by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma R532 : 4096 * 1 <= pgv E 532 <= 4096 * 34359736319.           Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R515 : 4096 * 1539 <= pgv E 515 <= 4096 * 34359734272.        Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R514 : 4096 * 1539 <= pgv E 514 <= 4096 * 34359736064.        Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R438 : 4096 * 1539 <= pgv E 438 <= 4096 * 34359733495.        Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R340 : 4096 * 1 <= pgv E 340 <= 4096 * 34359736319.           Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R275 : 4096 * 1 <= pgv E 275 <= 4096 * 34359736319.           Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R246 : 4096 * 1539 <= pgv E 246 <= 4096 * 34359736304.        Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R245 : 4096 * 1 <= pgv E 245 <= 4096 * 34359736319.           Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R244 : 4096 * 1539 <= pgv E 244 <= 4096 * 34359734272.        Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R226 : 4096 * 4295491576 <= pgv E 226 <= 4096 * 34326181871.  Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R227 : 4096 * 0 <= pgv E 227 <= 4096 * 15.                    Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R225 : 4096 * 1539 <= pgv E 225 <= 4096 * 34359735410.        Proof. apply pgv_range. vm_compute. reflexivity. Qed.
  Lemma R95 : 4096 * 1539 <= pgv E 95 <= 4096 * 34359736304.          Proof. apply pgv_range. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma init_halted : m_halted model = None.
  Proof. exact (main_halted sp rdraw brk0 hw argv envp fs uid E R FULL model hs HC). Qed.
  Lemma init_limit : vm_limit (m_vmmaps model) = target_alloc_limit.
  Proof. exact (main_limit sp rdraw brk0 hw argv envp fs uid E R FULL model hs HC). Qed.
  Lemma init_eager : eager_used model <= A_EB0.
  Proof.
    pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC) as H. unfold A_EB0.
    assert (X : a_eager hs <= 16515072) by (destruct Hhs as [-> | [-> | [-> | ->]]]; vm_compute; discriminate). lia.
  Qed.
  Lemma init_fds : m_fds model = fds_std.
  Proof. exact (main_fds sp rdraw brk0 hw argv envp fs uid E R FULL model hs Hhs HC). Qed.
  Lemma init_tid : exists t, m_tid model = Some t /\ 0 < bv_unsigned t < PID_MAX_ENVELOPE.
  Proof.
    apply (co_tidv _ _ _ _ _ _ _ _ _ _ _ HC). destruct Hhs as [-> | [-> | [-> | ->]]]; reflexivity.
  Qed.
  Lemma init_res : vm_reserved (m_vmmaps model) = segments_reserved BSEGS.
  Proof. exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma init_alloc_top : alloc_top (m_vmmaps model) = usp - 8388608.
  Proof.
    pose proof (cs_top BSEGS BOTH5 LIM SINV argH fs E hs R FULL model HC) as (_ & _ & T3).
    rewrite T3, (uE_sp0 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC). reflexivity.
  Qed.
  (* [comment removed for export] *)
  Let pusp := usp - usp mod 4096.
  Lemma u_psp0 : uE E e_psp0 = pusp.
  Proof. unfold pusp. rewrite (co_psp0 _ _ _ _ _ _ _ _ _ _ _ HC), (uE_sp0 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC). reflexivity. Qed.
  Lemma ptop_eq : ptop (m_vmmaps model) = pusp - 8388608.
  Proof. pose proof (cs_ptop BSEGS BOTH5 LIM SINV argH fs E hs R FULL model HC) as (_ & _ & P3 & _). rewrite P3, u_psp0. reflexivity. Qed.
  Lemma pusp_le : pusp <= usp /\ usp < pusp + 4096 /\ 0x7fff80000000 <= pusp /\ pusp mod 4096 = 0.
  Proof. pose proof (usp_lo sp Hsp). pose proof (Z.mod_pos_bound usp 4096 ltac:(lia)). unfold pusp. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma hs_maps : a_maps hs = a_maps HS_s2_00.
  Proof. destruct Hhs as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. Qed.
  Lemma hs_vis : a_vis hs = a_vis HS_s2_00.
  Proof. destruct Hhs as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. Qed.

  Lemma init_lazy_hull : forall e, In e (m_vm_lazy model) ->
    0 < bv_unsigned (snd e) /\
    (  (pgv E 515 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= pgv E 515 + 8388608)
    \/ (pgv E 244 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= pgv E 244 + 8388608)
    \/ (pgv E 226 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= pgv E 226 + 0x2000011000)
    \/ (0x2008fff7000 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 0x2008fff7000 + 15392894357504)
    \/ (0x8fff7000 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 0x8fff7000 + 2199023255552)
    \/ (0x7fff7000 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 0x7fff7000 + 268435456)).
  Proof.
    intros e He. pose proof (proj1 (Forall_forall _ _) (co_lhull _ _ _ _ _ _ _ _ _ _ _ HC) e He) as [P X]. split; [exact P|].
    pose proof R515 as R515. pose proof R244 as R244. pose proof R226 as R226.
    rewrite hs_maps in X. cbn [a_maps HS_s2_00] in X.
    repeat match type of X with
    | Exists _ (_ :: _) => apply Exists_cons in X; destruct X as [X|X]
    | Exists _ [] => apply Exists_nil in X; destruct X
    end;
    cbn [am_kind am_base am_len lz_kind] in X; destruct X as (Hk & L1 & L2); try discriminate Hk;
    change (EMd Instr.M_MUL (ELit 4096) (EVar 515)) with (pgE 515) in *;
    change (EMd Instr.M_MUL (ELit 4096) (EVar 244)) with (pgE 244) in *;
    change (EMd Instr.M_MUL (ELit 4096) (EVar 226)) with (pgE 226) in *;
    rewrite ?edenot_pg in L1 by lia; rewrite ?edenot_pg in L2 by lia;
    cbn [edenot] in L1, L2; rewrite ?u64_lit in L1 by lia; rewrite ?u64_lit in L2 by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lazy_clear_of : forall x n,
    x + n <= pgv E 515 \/ pgv E 515 + 8388608 <= x ->
    x + n <= pgv E 244 \/ pgv E 244 + 8388608 <= x ->
    x + n <= pgv E 226 \/ pgv E 226 + 0x2000011000 <= x ->
    x + n <= 0x7fff7000 \/ 0x10007fff8000 <= x ->
    AsanKern.clear_of (m_vm_lazy model) x n.
  Proof.
    intros x n D1 D2 D3 D4 e He. unfold AsanKern.elo, AsanKern.ehi. pose proof (init_lazy_hull e He). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pg_apart : forall v1 l1 v2 l2,
    (hs_fact (KDisj (SA (pgE v1) 0) (ELit l1) (SA (pgE v2) 0) (ELit l2)) || hs_fact (KDisj (SA (pgE v2) 0) (ELit l2) (SA (pgE v1) 0) (ELit l1)))%bool = true ->
    pgv E v1 < 2 ^ 64 -> pgv E v2 < 2 ^ 64 -> 0 <= l1 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 ->
    pgv E v1 + l1 <= pgv E v2 \/ pgv E v2 + l2 <= pgv E v1.
  Proof.
    intros v1 l1 v2 l2 HK H1 H2 Hl1 Hl2.
    apply orb_prop in HK as [HK|HK]; apply disj_fact in HK; rewrite !u_pg, !u_lit in HK by lia; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma pg_apart_zone : forall v l,
    hs_fact (KDisj (SA (pgE v) 0) (ELit l) (SA (ELit 0) 2147446784) (ELit 17592186048512)) = true ->
    pgv E v < 2 ^ 64 -> 0 <= l < 2 ^ 64 ->
    pgv E v + l <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E v.
  Proof. intros v l HK Hv Hl. apply disj_fact in HK. rewrite !u_pg, !u_lit in HK by lia. lia. Qed.
  (* [comment removed for export] *)
  Lemma pg_apart_img : forall v l,
    hs_fact (KDisj (SA (ELit 0) 65536) (ELit 6238208) (SA (pgE v) 0) (ELit l)) = true ->
    pgv E v < 2 ^ 64 -> 0 <= l < 2 ^ 64 ->
    pgv E v + l <= 0x10000 \/ 0x603000 <= pgv E v.
  Proof. intros v l HK Hv Hl. apply disj_fact in HK. rewrite !u_pg, !u_lit in HK by lia. lia. Qed.
  (* [comment removed for export] *)
  Lemma pg_apart_stack : forall v l,
    hs_fact (KDisj (SA e_psp0 (-8388608)) (ELit STACKWIN) (SA (pgE v) 0) (ELit l)) = true ->
    pgv E v < 2 ^ 64 -> 0 <= l < 2 ^ 64 ->
    pgv E v + l <= pusp - 8388608 \/ 2 ^ 47 <= pgv E v.
  Proof.
    intros v l HK Hv Hl. apply disj_fact in HK. rewrite u_psp0 in HK. rewrite !u_pg in HK by lia. rewrite !u_lit in HK by (unfold STACKWIN; lia).
    pose proof pusp_le. unfold STACKWIN in HK. unfold pgv in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma pg_apart_lit : forall v l b n,
    (hs_fact (KDisj (SA (pgE v) 0) (ELit l) (SA (ELit b) 0) (ELit n)) || hs_fact (KDisj (SA (ELit b) 0) (ELit n) (SA (pgE v) 0) (ELit l)))%bool = true ->
    pgv E v < 2 ^ 64 -> 0 <= l < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    pgv E v + l <= b \/ b + n <= pgv E v.
  Proof.
    intros v l b n HK Hv Hl Hb Hn.
    apply orb_prop in HK as [HK|HK]; apply disj_fact in HK; rewrite !u_pg, !u_lit in HK by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma space_beg_aligned : (pgv E 226 - pgv E 227 + 0x10000) mod 2 ^ 16 = 0.
  Proof.
    pose proof R226 as Ra'. pose proof R227 as Rb'.
    pose proof (FACT (KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 227)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 226)) (ELit 65535))) 0 0)
                  ltac:(vm_compute; reflexivity)) as [L1 L2].
    cbn [edenot] in L1, L2. unfold pgv in *.
    pose proof (u64_range (ev E 226)) as Ra. pose proof (u64_range (ev E 227)) as Rb.
    assert (UA : bv_unsigned (Sem.alu64 Instr.ALU_AND (Sem.mul_div Instr.M_MUL (Z_to_bv 64 4096) (ev E 226)) (Z_to_bv 64 65535)) = (4096 * bv_unsigned (ev E 226)) mod 2 ^ 16).
    { rewrite u_and64, u_mul64, !u64_lit by lia. rewrite (Z.mod_small (4096 * bv_unsigned (ev E 226))) by lia.
      change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. }
    assert (M0 : 2 ^ 64 <> 0) by (cbv; discriminate).
    assert (UM : bv_unsigned (Sem.mul_div Instr.M_MUL (Z_to_bv 64 (-4096)) (ev E 227)) = (2 ^ 64 - 4096 * bv_unsigned (ev E 227)) mod 2 ^ 64).
    { rewrite u_mul64. replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) by (vm_compute; reflexivity).
      replace ((2 ^ 64 - 4096) * bv_unsigned (ev E 227)) with ((2 ^ 64 - 4096 * bv_unsigned (ev E 227)) + (bv_unsigned (ev E 227) - 1) * 2 ^ 64) by lia.
      rewrite (Z.mod_add _ _ _ M0). reflexivity. }
    assert (US : bv_unsigned (Sem.alu64 Instr.ALU_ADD (Sem.mul_div Instr.M_MUL (Z_to_bv 64 (-4096)) (ev E 227))
                                (Sem.alu64 Instr.ALU_AND (Sem.mul_div Instr.M_MUL (Z_to_bv 64 4096) (ev E 226)) (Z_to_bv 64 65535))) = 0) by lia.
    rewrite u_add64, UA, UM in US.
    pose proof (Z.mod_pos_bound (4096 * bv_unsigned (ev E 226)) (2 ^ 16) ltac:(lia)) as MB.
    set (r16 := (4096 * bv_unsigned (ev E 226)) mod 2 ^ 16) in *.
    assert (E2 : 4096 * bv_unsigned (ev E 227) = r16).
    { destruct (Z.eq_dec (bv_unsigned (ev E 227)) 0) as [Z0|NZ].
      - rewrite Z0 in US |- *. rewrite Z.sub_0_r, Z.mod_same in US by lia. rewrite Z.add_0_l, Z.mod_small in US by lia. lia.
      - rewrite (Z.mod_small (2 ^ 64 - 4096 * bv_unsigned (ev E 227))) in US by lia.
        replace (2 ^ 64 - 4096 * bv_unsigned (ev E 227) + r16) with ((r16 - 4096 * bv_unsigned (ev E 227)) + 1 * 2 ^ 64) in US by lia.
        rewrite (Z.mod_add _ _ _ M0) in US.
        destruct (Z_lt_le_dec (r16 - 4096 * bv_unsigned (ev E 227)) 0) as [NEG|POS].
        + exfalso. replace (r16 - 4096 * bv_unsigned (ev E 227)) with ((2 ^ 64 + (r16 - 4096 * bv_unsigned (ev E 227))) + (-1) * 2 ^ 64) in US by lia.
          rewrite (Z.mod_add _ _ _ M0) in US. rewrite Z.mod_small in US by lia. lia.
        + rewrite Z.mod_small in US by lia. lia. }
    subst r16. clear US UA UM L1 L2 HC. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Definition e_rib : expr := EAlu Instr.ALU_ADD (pgE 226) (EMd Instr.M_MUL (ELit (-4096)) (EVar 227)).
  Lemma u_rib : uE E e_rib = pgv E 226 - pgv E 227.
  Proof.
    pose proof R226 as R226'. pose proof R227 as R227'.
    unfold uE, e_rib, pgE. cbn [edenot]. rewrite !u_add64, !u_mul64, !u64_lit by lia.
    replace (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 4096) by (vm_compute; reflexivity).
    unfold pgv in *. pose proof (u64_range (ev E 226%nat)) as Ra. pose proof (u64_range (ev E 227%nat)) as Rb.
    set (u1 := bv_unsigned (ev E 226%nat)) in *. set (u2 := bv_unsigned (ev E 227%nat)) in *.
    rewrite <- (Z.add_mod (4096 * u1) ((2 ^ 64 - 4096) * u2) (2 ^ 64)) by lia.
    replace (4096 * u1 + (2 ^ 64 - 4096) * u2) with ((4096 * u1 - 4096 * u2) + u2 * 2 ^ 64) by lia.
    assert (M0 : 2 ^ 64 <> 0) by (cbv; discriminate).
    rewrite (Z.mod_add _ _ _ M0). apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma amap_in_b : forall m, existsb (amap_eqb m) (a_maps HS_s2_00) = true -> In m (a_maps hs).
  Proof.
    intros m H. rewrite hs_maps. apply existsb_exists in H as (m' & Hin & Heq). apply APS.amap_eqb_eq in Heq. subst m'. exact Hin.
  Qed.
  Lemma amap_in_maps : forall b l k, existsb (amap_eqb (AM b l k)) (a_maps HS_s2_00) = true -> is_tok_kind k = false ->
    In (edenot E b, edenot E l) (vm_maps (m_vmmaps model)).
  Proof.
    intros b l k Hin Hk. apply amap_in_b in Hin.
    exact (maps_match_In E (a_maps hs) _ (AM b l k) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hin Hk).
  Qed.

  Lemma init_vm_maps : exists fog,
    vm_maps (m_vmmaps model) = l0_head E ++ fog ++ l0_tail E
    /\ Forall (fun e => bv_unsigned (snd e) <= 8192) fog /\ (length fog <= 2)%nat.
  Proof.
    pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM. rewrite hs_maps in MM.
    pose proof R532. pose proof R515. pose proof R514. pose proof R438. pose proof R340. pose proof R275. pose proof R246.
    pose proof R245. pose proof R244. pose proof R226. pose proof R225. pose proof R95.
    cbn [a_maps HS_s2_00 maps_match is_fog is_tok_kind am_kind] in MM.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 532)) with (pgE 532) in MM. change (EMd Instr.M_MUL (ELit 4096) (EVar 515)) with (pgE 515) in MM.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 514)) with (pgE 514) in MM. change (EMd Instr.M_MUL (ELit 4096) (EVar 438)) with (pgE 438) in MM.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 340)) with (pgE 340) in MM. change (EMd Instr.M_MUL (ELit 4096) (EVar 275)) with (pgE 275) in MM.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 246)) with (pgE 246) in MM. change (EMd Instr.M_MUL (ELit 4096) (EVar 245)) with (pgE 245) in MM.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 244)) with (pgE 244) in MM. change (EMd Instr.M_MUL (ELit 4096) (EVar 226)) with (pgE 226) in MM.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 225)) with (pgE 225) in MM. change (EMd Instr.M_MUL (ELit 4096) (EVar 95)) with (pgE 95) in MM.
    unfold amap_den in MM. cbn [am_base am_len] in MM. rewrite !edenot_pg in MM by lia. cbn [edenot] in MM.
    unfold uE in MM. cbn [edenot] in MM. rewrite !(u64_lit 8192) in MM by lia.
    destruct MM as (l1 & -> & l2 & -> & l3 & -> & MM).
    assert (FOGS : exists fog rest, l3 = fog ++ rest /\ Forall (fun e => bv_unsigned (snd e) <= 8192) fog /\ (length fog <= 2)%nat
                   /\ maps_match E (skipn 5 (a_maps HS_s2_00)) rest).
    { cbn [skipn a_maps HS_s2_00].
      destruct MM as [MM | (iv1 & l4 & -> & S1 & MM)]; destruct MM as [MM | (iv2 & l5 & -> & S2 & MM)].
      - exists [], l3. cbn. repeat split; auto; constructor.
      - exists [iv2], l5. repeat split; [constructor; [exact S2 | constructor] | cbn; lia | exact MM].
      - exists [iv1], l4. repeat split; [constructor; [exact S1 | constructor] | cbn; lia | exact MM].
      - exists [iv1; iv2], l5. repeat split; [constructor; [exact S1 | constructor; [exact S2 | constructor]] | cbn; lia | exact MM]. }
    destruct FOGS as (fog & rest & -> & FS & FL & MR). exists fog.
    cbn [skipn a_maps HS_s2_00 maps_match is_fog is_tok_kind am_kind] in MR.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 438)) with (pgE 438) in MR.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 340)) with (pgE 340) in MR. change (EMd Instr.M_MUL (ELit 4096) (EVar 275)) with (pgE 275) in MR.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 246)) with (pgE 246) in MR. change (EMd Instr.M_MUL (ELit 4096) (EVar 245)) with (pgE 245) in MR.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 244)) with (pgE 244) in MR. change (EMd Instr.M_MUL (ELit 4096) (EVar 226)) with (pgE 226) in MR.
    change (EMd Instr.M_MUL (ELit 4096) (EVar 225)) with (pgE 225) in MR. change (EMd Instr.M_MUL (ELit 4096) (EVar 95)) with (pgE 95) in MR.
    unfold amap_den in MR. cbn [am_base am_len] in MR. rewrite !edenot_pg in MR by lia. cbn [edenot] in MR.
    destruct MR as (r1 & -> & r2 & -> & r3 & -> & r4 & -> & r5 & -> & r6 & -> & r7 & -> & r8 & -> & r9 & -> & r10 & -> & r11 & -> & r12 & -> & ->).
    split; [reflexivity|]. split; [exact FS | exact FL].
  Qed.

  Lemma init_maps_bounds : Forall (fun e => 0 < bv_unsigned (snd e) /\ bv_unsigned (fst e) mod 4096 = 0 /\ bv_unsigned (snd e) mod 4096 = 0
                                    /\ 0 < bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= usp - 8388608) (vm_maps (m_vmmaps model)).
  Proof.
    pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as B. pose proof (co_bpos _ _ _ _ _ _ _ _ _ _ _ HC) as BP.
    pose proof ptop_eq as PT. pose proof pusp_le as PU.
    apply Forall_forall. intros e He.
    pose proof (proj1 (Forall_forall _ _) B e He) as X. pose proof (proj1 (Forall_forall _ _) BP e He) as Y. cbn beta in *. lia.
  Qed.

  Lemma init_maps_disjoint : forall l1 e1 l2 e2 l3, vm_maps (m_vmmaps model) = l1 ++ e1 :: l2 ++ e2 :: l3 ->
    bv_unsigned (fst e1) + bv_unsigned (snd e1) <= bv_unsigned (fst e2) \/ bv_unsigned (fst e2) + bv_unsigned (snd e2) <= bv_unsigned (fst e1).
  Proof.
    intros l1 e1 l2 e2 l3 HL. pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as S. rewrite HL in S. clear HL.
    induction l1 as [|a l1 IH]; cbn in S.
    - inversion S as [|p l F S']; subst. apply (proj1 (Forall_forall _ _) F e2). apply in_or_app. right. left. reflexivity.
    - inversion S as [|p l F S']; subst. exact (IH S').
  Qed.

  Lemma init_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= 17729664598016.
  Proof.
    pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as T.
    assert (X : a_totsz hs = 17729664598016) by (destruct Hhs as [-> | [-> | [-> | ->]]]; reflexivity). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma kwr_pointwise : forall be off l, hs_fact (KWr (SA be off) (ELit l)) = true ->
    0 <= uE E be + off -> (uE E be + off + l <= A_IMG_LO \/ A_IMG_HI <= uE E be + off) -> uE E be + off + l <= pusp - 8388608 ->
    forall z, uE E be + off <= z < uE E be + off + l ->
      in_ivs z (vm_maps (m_vmmaps model)) = true /\ in_ivs z (vm_noaccess (m_vmmaps model)) = false /\ FULL (Z_to_bv 64 z) <> None.
  Proof.
    intros be off l HK Hlo Hhull Hhi z Hz. pose proof (FACT _ HK) as [_ HW]. unfold A_IMG_LO, A_IMG_HI in Hhull.
    pose proof (usp_lo sp Hsp) as UL. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH. pose proof pusp_le as PU.
    pose proof ptop_eq as PT.
    unfold estart, elenZ in HW. cbn [a_base a_off edenot] in HW. change (bv_unsigned (edenot E be)) with (uE E be) in HW.
    rewrite u64_lit in HW by (unfold usp in *; lia).
    specialize (HW (z - (uE E be + off)) 1%nat ltac:(lia) ltac:(cbn; lia)).
    replace (uE E be + off + (z - (uE E be + off))) with z in HW by lia.
    pose proof (StoreOk.store_ok_all BSEGS MR 1%nat (Z_to_bv 64 z) ltac:(rewrite u64_lit by (unfold usp in *; lia); cbn; unfold usp in *; lia) HW (Z_to_bv 64 z) ltac:(cbn; lia)) as HV.
    change BSEGS with AImages.bsegs in HV.
    rewrite (AImageFacts.both_wview_overlay MR (Z_to_bv 64 z)) in HV by (rewrite u64_lit by (unfold usp in *; lia); lia).
    destruct (MR (Z_to_bv 64 z)) as [b|] eqn:Hm; [| exfalso; exact (HV eq_refl)]. clear HW HV.
    unfold Mr, mrestrict in Hm. destruct (hid BOTH5 argH E hs model (Z_to_bv 64 z)) eqn:Hh; [discriminate Hm|].
    unfold hid in Hh. apply Bool.orb_false_iff in Hh as [_ Hv]. apply Bool.negb_false_iff in Hv. unfold vis in Hv.
    rewrite u64_lit in Hv by (unfold usp in *; lia).
    replace (in_hull BOTH5 z) with false in Hv by (symmetry; unfold in_hull; cbn [img_lo img_hi BOTH5]; apply Bool.andb_false_iff; destruct Hhull; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    rewrite PT in Hv. replace (pusp - 8388608 <=? z) with false in Hv by (symmetry; apply Z.leb_gt; lia).
    cbn [orb] in Hv. apply andb_prop in Hv as [Hv _]. apply andb_prop in Hv as [H1 H2]. apply Bool.negb_true_iff in H2.
    split; [exact H1|]. split; [exact H2|]. rewrite Hm. discriminate.
  Qed.
  Lemma kwr_pg_pointwise : forall v l, hs_fact (KWr (SA (pgE v) 0) (ELit l)) = true ->
    (pgv E v + l <= A_IMG_LO \/ A_IMG_HI <= pgv E v) -> pgv E v + l <= pusp - 8388608 ->
    forall z, pgv E v <= z < pgv E v + l ->
      in_ivs z (vm_maps (m_vmmaps model)) = true /\ in_ivs z (vm_noaccess (m_vmmaps model)) = false /\ FULL (Z_to_bv 64 z) <> None.
  Proof.
    intros v l HK Hhull Hhi z Hz. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH. pose proof pusp_le as PU.
    assert (U : uE E (pgE v) = pgv E v) by (apply u_pg; unfold usp in *; lia).
    pose proof (kwr_pointwise (pgE v) 0 l HK) as X. rewrite U, !Z.add_0_r in X. pose proof R532.
    apply X; [unfold pgv; pose proof (u64_range (ev E v)); lia | exact Hhull | exact Hhi | exact Hz].
  Qed.

  (* [comment removed for export] *)
  Lemma clear_ofp_of_pointwise : forall x n, 0 < n ->
    (forall z, x <= z < x + n -> in_ivs z (vm_noaccess (m_vmmaps model)) = false) ->
    AsanKern.clear_ofp (vm_noaccess (m_vmmaps model)) x n.
  Proof.
    intros x n Hn HP e He Hpos. unfold AsanKern.elo, AsanKern.ehi.
    destruct (Z_lt_le_dec (Z.max x (bv_unsigned (fst e))) (Z.min (x + n) (bv_unsigned (fst e) + bv_unsigned (snd e)))) as [Hov|Hok]; [|lia].
    exfalso. specialize (HP (Z.max x (bv_unsigned (fst e))) ltac:(lia)).
    assert (T : in_ivs (Z.max x (bv_unsigned (fst e))) (vm_noaccess (m_vmmaps model)) = true); [|congruence].
    apply AsanNodesMmLib.in_ivs_true'. exists e. split; [exact He | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma shadow_lo_clear : AsanKern.clear_ofp (vm_noaccess (m_vmmaps model)) 0x7fff7000 268435456.
  Proof.
    apply clear_ofp_of_pointwise; [lia|]. intros z Hz.
    pose proof (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) _
                  (amap_in_b (AM (ELit 0x7fff7000) (ELit 268435456) KRWLAZY) ltac:(vm_compute; reflexivity)) eq_refl (Z_to_bv 64 z)) as X.
    cbn [am_base am_len edenot] in X. rewrite !u64_lit in X by lia. exact (proj1 (X Hz)).
  Qed.
  Lemma shadow_hi_clear : AsanKern.clear_ofp (vm_noaccess (m_vmmaps model)) 0x2008fff7000 15392894357504.
  Proof.
    apply clear_ofp_of_pointwise; [lia|]. intros z Hz.
    pose proof (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) _
                  (amap_in_b (AM (ELit 0x2008fff7000) (ELit 15392894357504) KRWLAZY) ltac:(vm_compute; reflexivity)) eq_refl (Z_to_bv 64 z)) as X.
    cbn [am_base am_len edenot] in X. rewrite !u64_lit in X by lia. exact (proj1 (X Hz)).
  Qed.
  Lemma init_shband_clear : forall e, In e (vm_noaccess (m_vmmaps model)) -> 0 < bv_unsigned (snd e) ->
    (AsanKern.ehi e <= 0x7fff7000 \/ 0x8fff7000 <= AsanKern.elo e) /\ (AsanKern.ehi e <= 0x2008fff7000 \/ 0x10007fff8000 <= AsanKern.elo e).
  Proof.
    intros e He Hpos. pose proof (shadow_lo_clear e He Hpos) as C1. pose proof (shadow_hi_clear e He Hpos) as C2.
    unfold AsanKern.elo, AsanKern.ehi in *. lia.
  Qed.

  Lemma INS : forall b l x n, In (Z_to_bv 64 b, Z_to_bv 64 l) (vm_maps (m_vmmaps model)) -> 0 <= b -> 0 <= l -> b + l < 2 ^ 64 ->
    b <= x -> x + n <= b + l -> AsanKern.inside (vm_maps (m_vmmaps model)) x n.
  Proof.
    intros b l x n Hin Hb Hl Hbl Hx Hn. exists (Z_to_bv 64 b, Z_to_bv 64 l). split; [exact Hin|].
    unfold AsanKern.elo, AsanKern.ehi. cbn [fst snd]. rewrite !u64_lit by lia. lia.
  Qed.

  Lemma get_region0 : forall c, AsanState.get_region (AsanState.astate0 (aenv_of hs E)) c = AsanState.region0.
  Proof. intros c. unfold AsanState.get_region. cbn [AsanState.as_regions AsanState.astate0]. rewrite fin_maps.lookup_empty. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma Z245 : pgv E 245 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 245.
  Proof. pose proof R245. apply pg_apart_zone; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma Z246 : pgv E 246 + 65536 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 246.
  Proof. pose proof R246. apply pg_apart_zone; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma Z438 : pgv E 438 + 11571200 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 438.
  Proof. pose proof R438. apply pg_apart_zone; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma Z515 : pgv E 515 + 8388608 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 515.
  Proof. pose proof R515. apply pg_apart_zone; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma Z514 : pgv E 514 + 1048576 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 514.
  Proof. pose proof R514. apply pg_apart_zone; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma Z244 : pgv E 244 + 8388608 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 244.
  Proof. pose proof R244. apply pg_apart_zone; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma Z340 : pgv E 340 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= pgv E 340.
  Proof. pose proof R340. apply pg_apart_zone; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma S245 : pgv E 245 + 4096 <= pusp - 8388608.
  Proof. pose proof R245. destruct (pg_apart_stack 245 4096 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma S246 : pgv E 246 + 65536 <= pusp - 8388608.
  Proof. pose proof R246. destruct (pg_apart_stack 246 65536 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma S438 : pgv E 438 + 11571200 <= pusp - 8388608.
  Proof. pose proof R438. destruct (pg_apart_stack 438 11571200 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma S515 : pgv E 515 + 8388608 <= pusp - 8388608.
  Proof. pose proof R515. destruct (pg_apart_stack 515 8388608 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma S514 : pgv E 514 + 1048576 <= pusp - 8388608.
  Proof. pose proof R514. destruct (pg_apart_stack 514 1048576 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma S244 : pgv E 244 + 8388608 <= pusp - 8388608.
  Proof. pose proof R244. destruct (pg_apart_stack 244 8388608 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma S340 : pgv E 340 + 4096 <= pusp - 8388608.
  Proof. pose proof R340. destruct (pg_apart_stack 340 4096 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma S226 : pgv E 226 + 0x2000011000 <= pusp - 8388608.
  Proof. pose proof R226. destruct (pg_apart_stack 226 0x2000011000 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)); lia. Qed.
  Lemma I245 : pgv E 245 + 4096 <= 0x10000 \/ 0x603000 <= pgv E 245.
  Proof. pose proof R245. apply pg_apart_img; [vm_compute; reflexivity | lia | lia]. Qed.
  Lemma I340 : pgv E 340 + 4096 <= 0x10000 \/ 0x603000 <= pgv E 340.
  Proof. pose proof R340. apply pg_apart_img; [vm_compute; reflexivity | lia | lia]. Qed.
  (* [comment removed for export] *)
  #[local] Ltac pga v1 l1 v2 l2 := apply (pg_apart v1 l1 v2 l2); [vm_compute; reflexivity | lia | lia | lia | lia].
  Lemma D226_245 : pgv E 226 + 0x2000011000 <= pgv E 245 \/ pgv E 245 + 4096 <= pgv E 226.   Proof. pose proof R226; pose proof R245. pga 226%nat 0x2000011000 245%nat 4096. Qed.
  Lemma D244_245 : pgv E 244 + 8388608 <= pgv E 245 \/ pgv E 245 + 4096 <= pgv E 244.        Proof. pose proof R244; pose proof R245. pga 244%nat 8388608 245%nat 4096. Qed.
  Lemma D515_245 : pgv E 515 + 8388608 <= pgv E 245 \/ pgv E 245 + 4096 <= pgv E 515.        Proof. pose proof R515; pose proof R245. pga 515%nat 8388608 245%nat 4096. Qed.
  Lemma D226_514 : pgv E 226 + 0x2000011000 <= pgv E 514 \/ pgv E 514 + 1048576 <= pgv E 226. Proof. pose proof R226; pose proof R514. pga 226%nat 0x2000011000 514%nat 1048576. Qed.
  Lemma D244_514 : pgv E 244 + 8388608 <= pgv E 514 \/ pgv E 514 + 1048576 <= pgv E 244.     Proof. pose proof R244; pose proof R514. pga 244%nat 8388608 514%nat 1048576. Qed.
  Lemma D515_514 : pgv E 515 + 8388608 <= pgv E 514 \/ pgv E 514 + 1048576 <= pgv E 515.     Proof. pose proof R515; pose proof R514. pga 515%nat 8388608 514%nat 1048576. Qed.
  Lemma D515_226 : pgv E 515 + 8388608 <= pgv E 226 \/ pgv E 226 + 0x2000011000 <= pgv E 515. Proof. pose proof R515; pose proof R226. pga 515%nat 8388608 226%nat 0x2000011000. Qed.
  Lemma D515_244 : pgv E 515 + 8388608 <= pgv E 244 \/ pgv E 244 + 8388608 <= pgv E 515.     Proof. pose proof R515; pose proof R244. pga 515%nat 8388608 244%nat 8388608. Qed.
  Lemma D245_514 : pgv E 245 + 4096 <= pgv E 514 \/ pgv E 514 + 1048576 <= pgv E 245.        Proof. pose proof R245; pose proof R514. pga 245%nat 4096 514%nat 1048576. Qed.
  Lemma D244_226 : pgv E 244 + 8388608 <= pgv E 226 \/ pgv E 226 + 0x2000011000 <= pgv E 244. Proof. pose proof R244; pose proof R226. pga 244%nat 8388608 226%nat 0x2000011000. Qed.
  Lemma D438_226 : pgv E 438 + 11571200 <= pgv E 226 \/ pgv E 226 + 0x2000011000 <= pgv E 438. Proof. pose proof R438; pose proof R226. pga 438%nat 11571200 226%nat 0x2000011000. Qed.
  Lemma D438_245 : pgv E 438 + 11571200 <= pgv E 245 \/ pgv E 245 + 4096 <= pgv E 438.       Proof. pose proof R438; pose proof R245. pga 438%nat 11571200 245%nat 4096. Qed.
  Lemma D438_244 : pgv E 438 + 11571200 <= pgv E 244 \/ pgv E 244 + 8388608 <= pgv E 438.    Proof. pose proof R438; pose proof R244. pga 438%nat 11571200 244%nat 8388608. Qed.
  Lemma D438_515 : pgv E 438 + 11571200 <= pgv E 515 \/ pgv E 515 + 8388608 <= pgv E 438.    Proof. pose proof R438; pose proof R515. pga 438%nat 11571200 515%nat 8388608. Qed.
  Lemma D438_514 : pgv E 438 + 11571200 <= pgv E 514 \/ pgv E 514 + 1048576 <= pgv E 438.    Proof. pose proof R438; pose proof R514. pga 438%nat 11571200 514%nat 1048576. Qed.
  Lemma D438_246 : pgv E 438 + 11571200 <= pgv E 246 \/ pgv E 246 + 65536 <= pgv E 438.      Proof. pose proof R438; pose proof R246. pga 438%nat 11571200 246%nat 65536. Qed.
  Lemma D245_244 : pgv E 245 + 4096 <= pgv E 244 \/ pgv E 244 + 8388608 <= pgv E 245.        Proof. pose proof R245; pose proof R244. pga 245%nat 4096 244%nat 8388608. Qed.
  Lemma D246_226 : pgv E 246 + 65536 <= pgv E 226 \/ pgv E 226 + 0x2000011000 <= pgv E 246.   Proof. pose proof R246; pose proof R226. pga 246%nat 65536 226%nat 0x2000011000. Qed.
  Lemma D246_514 : pgv E 246 + 65536 <= pgv E 514 \/ pgv E 514 + 1048576 <= pgv E 246.      Proof. pose proof R246; pose proof R514. pga 246%nat 65536 514%nat 1048576. Qed.
  Lemma D246_515 : pgv E 246 + 65536 <= pgv E 515 \/ pgv E 515 + 8388608 <= pgv E 246.      Proof. pose proof R246; pose proof R515. pga 246%nat 65536 515%nat 8388608. Qed.
  Lemma D246_245 : pgv E 246 + 65536 <= pgv E 245 \/ pgv E 245 + 4096 <= pgv E 246.         Proof. pose proof R246; pose proof R245. pga 246%nat 65536 245%nat 4096. Qed.
  Lemma D246_244 : pgv E 246 + 65536 <= pgv E 244 \/ pgv E 244 + 8388608 <= pgv E 246.      Proof. pose proof R246; pose proof R244. pga 246%nat 65536 244%nat 8388608. Qed.
  Lemma D246_438 : pgv E 246 + 65536 <= pgv E 438 \/ pgv E 438 + 11571200 <= pgv E 246.     Proof. pose proof R246; pose proof R438. pga 246%nat 65536 438%nat 11571200. Qed.
  Lemma D340_226 : pgv E 340 + 4096 <= pgv E 226 \/ pgv E 226 + 0x2000011000 <= pgv E 340.   Proof. pose proof R340; pose proof R226. pga 340%nat 4096 226%nat 0x2000011000. Qed.
  Lemma D340_438 : pgv E 340 + 4096 <= pgv E 438 \/ pgv E 438 + 11571200 <= pgv E 340.      Proof. pose proof R340; pose proof R438. pga 340%nat 4096 438%nat 11571200. Qed.
  Lemma D340_515 : pgv E 340 + 4096 <= pgv E 515 \/ pgv E 515 + 8388608 <= pgv E 340.       Proof. pose proof R340; pose proof R515. pga 340%nat 4096 515%nat 8388608. Qed.
  Lemma D340_244 : pgv E 340 + 4096 <= pgv E 244 \/ pgv E 244 + 8388608 <= pgv E 340.       Proof. pose proof R340; pose proof R244. pga 340%nat 4096 244%nat 8388608. Qed.
  Lemma D340_514 : pgv E 340 + 4096 <= pgv E 514 \/ pgv E 514 + 1048576 <= pgv E 340.       Proof. pose proof R340; pose proof R514. pga 340%nat 4096 514%nat 1048576. Qed.
  Lemma D340_245 : pgv E 340 + 4096 <= pgv E 245 \/ pgv E 245 + 4096 <= pgv E 340.          Proof. pose proof R340; pose proof R245. pga 340%nat 4096 245%nat 4096. Qed.
  Lemma D340_246 : pgv E 340 + 4096 <= pgv E 246 \/ pgv E 246 + 65536 <= pgv E 340.         Proof. pose proof R340; pose proof R246. pga 340%nat 4096 246%nat 65536. Qed.

  (* [comment removed for export] *)
  Context {RC__ : RunCeiling.RunCeiling}.
  Hypothesis RCSP : RunCeiling.rc_sp = usp.
  Lemma ceil_eq : RunCeiling.alloc_ceiling = usp - 8388608.
  Proof.
    pose proof (usp_lo sp Hsp). pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit).
    unfold RunCeiling.alloc_ceiling. rewrite RCSP. unfold usp in *. lia.
  Qed.

  Theorem init_akern : AsanKern.AKern (aenv_of hs E) (AsanState.astate0 (aenv_of hs E)) model.
  Proof.
    pose proof R515 as R515'. pose proof R514 as R514'. pose proof R245 as R245'. pose proof R244 as R244'. pose proof R226 as R226'. pose proof R227 as R227'.
    pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH. pose proof (usp_lo sp Hsp) as UL. pose proof ceil_eq as CE. pose proof pusp_le as PU.
    assert (IN226 := amap_in_maps (pgE 226) (ELit 137439023104) KMIX ltac:(vm_compute; reflexivity) eq_refl).
    assert (IN244 := amap_in_maps (pgE 244) (ELit 8388608) KNONELAZY ltac:(vm_compute; reflexivity) eq_refl).
    assert (IN245 := amap_in_maps (pgE 245) (ELit 4096) KRW ltac:(vm_compute; reflexivity) eq_refl).
    assert (IN514 := amap_in_maps (pgE 514) (ELit 1048576) KRW ltac:(vm_compute; reflexivity) eq_refl).
    assert (IN515 := amap_in_maps (pgE 515) (ELit 8388608) KRWLAZY ltac:(vm_compute; reflexivity) eq_refl).
    rewrite !edenot_pg in IN226, IN244, IN245, IN514, IN515 by (unfold usp in *; lia). cbn [edenot] in IN226, IN244, IN245, IN514, IN515.
    pose proof (kwr_pg_pointwise 245 4096 ltac:(vm_compute; reflexivity) ltac:(unfold A_IMG_LO, A_IMG_HI; pose proof I245; lia) S245) as W245.
    pose proof (kwr_pg_pointwise 514 1048576 ltac:(vm_compute; reflexivity) ltac:(unfold A_IMG_LO, A_IMG_HI; lia) S514) as W514.
    pose proof (kwr_pg_pointwise 515 8388608 ltac:(vm_compute; reflexivity) ltac:(unfold A_IMG_LO, A_IMG_HI; lia) S515) as W515.
    pose proof u_rib as URI.
    pose proof (kwr_pointwise e_rib 137439019008 4096 ltac:(vm_compute; reflexivity) ltac:(rewrite URI; lia) ltac:(rewrite URI; unfold A_IMG_LO, A_IMG_HI; lia) ltac:(rewrite URI; pose proof S226; lia)) as WRI.
    rewrite URI in WRI.
    pose proof D226_245 as D1. pose proof D244_245 as D2. pose proof D515_245 as D3. pose proof D226_514 as D4. pose proof D244_514 as D5. pose proof D515_514 as D6.
    pose proof D515_226 as D7. pose proof D515_244 as D8. pose proof D245_514 as D9. pose proof Z245 as Y1. pose proof Z514 as Y2.
    constructor; cbn [AsanState.ae_resv_beg AsanState.ae_space_beg AsanState.ae_ptr_array AsanState.ae_thread AsanState.ae_depot_nodes
                      AsanState.ae_store_blk AsanState.ae_reserved aenv_of
                      AsanState.as_ptr_committed AsanState.as_sec AsanState.as_node_blocks AsanState.as_store_blocks AsanState.astate0];
      unfold AsanKern.went, AsanKern.kwz, AsanKern.kResvLen, AsanKern.kPtrArrayLen, AsanKern.eager_rw,
             AsanSizeClass.kSpaceSize, AsanSizeClass.kPageSize, AsanSizeClass.kPtrArrayCommit, AsanSizeClass.kChunksBlockCount,
             AsanConsts.kDepotNodeBlockBytes, AsanConsts.kStoreBlockBytes.
    - (* [comment removed for export] *) exact IN226.
    - (* [comment removed for export] *) split; [lia|]. split; [exact space_beg_aligned | lia].
    - (* [comment removed for export] *) split.
      + apply (INS (pgv E 226) 137439023104); try lia. exact IN226.
      + apply clear_ofp_of_pointwise; [lia|]. intros z Hz. apply (proj1 (proj2 (WRI z ltac:(lia)))).
    - (* [comment removed for export] *) intros c _ Hc. rewrite get_region0 in Hc. cbn in Hc. lia.
    - (* [comment removed for export] *) intros c _ Hc. rewrite get_region0 in Hc. cbn in Hc. lia.
    - (* [comment removed for export] *) exact IN244.
    - (* [comment removed for export] *) cbn. intros H. discriminate H.
    - (* [comment removed for export] *) cbn [Z.eqb]. intros p Hp1 Hp2 Hal.
      assert (NN : In (amap_den E (AM (pgE 244) (ELit 8388608) KNONELAZY)) (vm_noaccess (m_vmmaps model))).
      { apply (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC)); [apply amap_in_b; vm_compute; reflexivity | right; reflexivity]. }
      unfold amap_den in NN. cbn [am_base am_len] in NN. rewrite edenot_pg in NN by lia. cbn [edenot] in NN.
      exists (Z_to_bv 64 (pgv E 244), Z_to_bv 64 8388608). split; [exact NN|]. unfold AsanKern.elo, AsanKern.ehi. cbn [fst snd]. rewrite !u64_lit by lia. lia.
    - (* [comment removed for export] *) intros sc Hsc. destruct Hsc.
    - (* [comment removed for export] *) split; [apply (INS (pgv E 245) 4096); try lia; exact IN245|]. split.
      + apply clear_ofp_of_pointwise; [lia|]. intros z Hz. apply (proj1 (proj2 (W245 z Hz))).
      + apply lazy_clear_of; lia.
    - (* [comment removed for export] *) split; [apply (INS (pgv E 514) 1048576); try lia; exact IN514|]. split.
      + apply clear_ofp_of_pointwise; [lia|]. intros z Hz. apply (proj1 (proj2 (W514 z Hz))).
      + apply lazy_clear_of; lia.
    - (* [comment removed for export] *) split; [apply (INS (pgv E 515) 8388608); try lia; exact IN515|].
      apply clear_ofp_of_pointwise; [lia|]. intros z Hz. apply (proj1 (proj2 (W515 z Hz))).
    - (* [comment removed for export] *) intros b Hb. destruct Hb.
    - (* [comment removed for export] *) intros b Hb. destruct Hb.
    - (* [comment removed for export] *) intros b len [[Hb _]|[Hb _]]; destruct Hb.
    - (* [comment removed for export] *) intros e He. unfold AsanKern.elo, AsanKern.ehi. rewrite AsanSizeClass.kHighMemBeg_val. cbn [Z.eqb].
      pose proof (init_lazy_hull e He) as [_ L].
      destruct L as [L|[L|[L|[L|[L|L]]]]].
      + right; left. lia.
      + right; right; right; left. lia.
      + right; right; right; right. split; [lia|]. split; [lia|]. split; intros c _ Hc; rewrite get_region0 in Hc; cbn in Hc; lia.
      + left. lia.
      + left. lia.
      + left. lia.
    - (* [comment removed for export] *) split; [lia|]. split; [intros sc Hsc; destruct Hsc|]. split; [lia|]. split; [lia|]. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_kvm : B_slack5.KVM (l0_of E) (segments_reserved BSEGS) model (AsanState.astate0 (aenv_of hs E)).
  Proof.
    pose proof ceil_eq as CE. pose proof pusp_le as PU.
    unfold B_slack5.KVM. split; [exact init_res|]. split.
    - destruct init_vm_maps as (fog & Hvm & Hsz & Hlen). exists fog. split; [| exact (conj Hsz Hlen)].
      rewrite Hvm, B_bundle.amaps_init, app_nil_r. unfold l0_of. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
    - split.
      + (* [comment removed for export] *) split.
        * intros i j e1 e2 Hi Hj Hij. unfold AsanKern.elo, AsanKern.ehi.
          destruct (Nat.lt_ge_cases i j) as [L|G].
          -- destruct (nth_error_split _ _ Hi) as (l1 & l2 & HL & Hl1).
             assert (Hj' : nth_error l2 (j - i - 1) = Some e2).
             { rewrite HL in Hj. rewrite nth_error_app2 in Hj by lia. rewrite Hl1 in Hj. replace (j - i)%nat with (Datatypes.S (j - i - 1))%nat in Hj by lia. cbn [nth_error] in Hj. exact Hj. }
             destruct (nth_error_split _ _ Hj') as (l3 & l4 & HL2 & _). rewrite HL2 in HL.
             exact (init_maps_disjoint l1 e1 l3 e2 l4 HL).
          -- destruct (nth_error_split _ _ Hj) as (l1 & l2 & HL & Hl1).
             assert (Hi' : nth_error l2 (i - j - 1) = Some e1).
             { rewrite HL in Hi. rewrite nth_error_app2 in Hi by lia. rewrite Hl1 in Hi. replace (i - j)%nat with (Datatypes.S (i - j - 1))%nat in Hi by lia. cbn [nth_error] in Hi. exact Hi. }
             destruct (nth_error_split _ _ Hi') as (l3 & l4 & HL2 & _). rewrite HL2 in HL.
             pose proof (init_maps_disjoint l1 e2 l3 e1 l4 HL). lia.
        * pose proof init_maps_bounds as B. unfold AsanKern.elo, AsanKern.ehi. rewrite CE.
          apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) B e He). cbn beta in *. lia.
      + split; [exact (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)|]. split.
        * (* [comment removed for export] *) intros e He. unfold AsanKern.elo, AsanKern.ehi. destruct (co_nao _ _ _ _ _ _ _ _ _ _ _ HC e He) as [H1 (m0 & Hm0 & H2 & H3)].
          split; [exact H1|]. exists m0. split; [exact Hm0|]. split; [exact H2 |].
          first [exact H3 | split; [exact H3 | exact (init_shband_clear e He H1)]].
        * rewrite init_alloc_top, CE. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem init_minvA : NodesA.minvA model.
  Proof.
    pose proof init_fds as FD. destruct init_tid as (t & Ht & Htr).
    assert (LK : forall k e, fd_lookup fds_std k = Some e -> exists c, e = FdChannel c /\ bv_unsigned k < 3).
    { intros k e Hk. unfold fds_std in Hk. cbn [fd_lookup] in Hk.
      destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. injection Hk as <-. exists (Z_to_bv 64 0). split; [reflexivity | vm_compute; reflexivity]. }
      destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. injection Hk as <-. exists (Z_to_bv 64 1). split; [reflexivity | vm_compute; reflexivity]. }
      destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. injection Hk as <-. exists (Z_to_bv 64 2). split; [reflexivity | vm_compute; reflexivity]. }
      discriminate Hk. }
    unfold NodesA.minvA. rewrite FD.
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [intros k c Hk; destruct (LK k _ Hk) as (c' & _ & Hlt); exact Hlt|].
    split; [intros k p off Hk; destruct (LK k _ Hk) as (c' & Hc & _); discriminate Hc|].
    split; [intros k e Hk; destruct (LK k _ Hk) as (c' & -> & _); exact I|].
    split; [intros t' Ht'; rewrite Ht in Ht'; injection Ht' as <-; exact Htr|].
    rewrite init_alloc_top, ceil_eq. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma res0_val : segments_reserved BSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x21000); (Z_to_bv 64 0x31000, Z_to_bv 64 0x74000);
                                             (Z_to_bv 64 0xa5000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xa7000, Z_to_bv 64 0x55c000)].
  Proof. vm_compute. reflexivity. Qed.

  Theorem init_l0_ok : B_benv5.l0_ok5 (aenv_of hs E) (l0_of E) (segments_reserved BSEGS).
  Proof.
    pose proof R532. pose proof R515. pose proof R514. pose proof R438. pose proof R340. pose proof R275. pose proof R246.
    pose proof R245. pose proof R244. pose proof R226. pose proof R225. pose proof R95.
    unfold B_benv5.l0_ok5. unfold AsanKern.elo, AsanKern.ehi. rewrite res0_val.
    split; [unfold l0_of, l0_tail; apply in_app_iff; right; cbn [In]; inlist|].
    split; [unfold l0_of, l0_tail; apply in_app_iff; right; cbn [In]; inlist|].
    split; [unfold l0_of, l0_tail; apply in_app_iff; right; cbn [In]; inlist|].
    split; [repeat (apply Forall_cons; [cbn [fst snd]; rewrite !u64_lit by lia; lia|]); apply Forall_nil|].
    split.
    { intros x Hx.
      destruct (Z_lt_le_dec x 0x31000); [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x21000); split; [cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
      destruct (Z_lt_le_dec x 0xa5000); [exists (Z_to_bv 64 0x31000, Z_to_bv 64 0x74000); split; [cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
      destruct (Z_lt_le_dec x 0xa7000); [exists (Z_to_bv 64 0xa5000, Z_to_bv 64 0x2000); split; [cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
      exists (Z_to_bv 64 0xa7000, Z_to_bv 64 0x55c000); split; [cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia]. }
    split.
    { intros rr x Hrr Hx. cbn [AsanState.ae_reserved aenv_of] in Hrr. unfold reserved_of, A_IMG in Hrr. left.
      (* [comment removed for export] *)
      Ltac l0w b l := exists (Z_to_bv 64 b, Z_to_bv 64 l); split; [apply in_app_iff; right; unfold l0_of, l0_head, l0_tail; cbn [In app]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia].
      repeat (destruct Hrr as [<-|Hrr]; [cbn [fst snd] in Hx|]).
      - l0w (pgv E 245) 4096.
      - l0w (pgv E 246) 65536.
      - l0w (pgv E 438) 11571200.
      - l0w (pgv E 515) 8388608.
      - l0w (pgv E 514) 1048576.
      - l0w (pgv E 244) 8388608.
      - l0w (pgv E 226) 0x2000011000.
      - l0w (pgv E 340) 4096.
      - l0w (pgv E 275) 4096.
      - l0w (pgv E 532) 4096.
      - l0w (pgv E 225) 3727360.
      - l0w (pgv E 95) 65536.
      - l0w 0x7fff7000 268435456.
      - l0w 0x8fff7000 2199023255552.
      - l0w 0x2008fff7000 15392894357504.
      - (* [comment removed for export] *)
        destruct (Z_lt_le_dec x 0x31000); [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x21000); split; [apply in_app_iff; left; cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
        destruct (Z_lt_le_dec x 0xa5000); [exists (Z_to_bv 64 0x31000, Z_to_bv 64 0x74000); split; [apply in_app_iff; left; cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
        destruct (Z_lt_le_dec x 0xa7000); [exists (Z_to_bv 64 0xa5000, Z_to_bv 64 0x2000); split; [apply in_app_iff; left; cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
        exists (Z_to_bv 64 0xa7000, Z_to_bv 64 0x55c000); split; [apply in_app_iff; left; cbn [In]; inlist | cbn [fst snd]; rewrite !u64_lit by lia; lia].
      - destruct Hrr. }
    cbn [AsanState.ae_reserved aenv_of]. unfold reserved_of, A_IMG. repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma img_ranges_asan : forall r, In r (AsanRepFrame.arep_img_ranges (aenv_of hs E) ++ AsanRepFrame.depot_static (aenv_of hs E)) ->
    0x10000 <= fst r /\ fst r + snd r <= 0x603000
    /\ (forall x, fst r <= x < fst r + snd r -> ~ B_benv5.cl_cells x /\ ~ B_benv5.stdio_w x).
  Proof.
    intros r Hr. remember (aenv_of hs E) as E0 eqn:HE0.
    assert (IC0 : AsanState.ae_ic E0 = AsanConsts.both_ic) by (subst E0; reflexivity). clear HE0.
    unfold AsanRepFrame.arep_img_ranges, AsanRepFrame.depot_static, AsanState.ae_instance in Hr. rewrite IC0 in Hr. cbn -[Z.add Z.mul Z.le] in Hr.
    unfold B_benv5.cl_cells, B_benv5.stdio_w. cbn [B_base.c_initialized B_base.c_errno B_base.c_stderr_F B_base.c_stdout_F B_base.c_stdout_buf B_base.ACONSTS].
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; split; [lia|]; split; [lia|]; intros x Hx; split; clear -Hx; lia|]). destruct Hr.
  Qed.

  Lemma stack_top_range : 0 <= AsanState.ae_stack_bottom (aenv_of hs E) /\ AsanState.ae_stack_bottom (aenv_of hs E) < AsanState.ae_stack_top (aenv_of hs E) <= 2 ^ 47.
  Proof.
    pose proof (usp_lo sp Hsp) as UL. pose proof (usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as UH.
    unfold AsanState.ae_stack_bottom, AsanState.ae_stack_top. cbn [AsanState.ae_sp0 aenv_of].
    change (bv_unsigned (edenot E e_sp0)) with (uE E e_sp0). rewrite (uE_sp0 sp rdraw brk0 hw argv envp fs uid Hsp Hva Hve Hfit E R FULL model hs HC).
    unfold AsanSizeClass.round_up, AsanConsts.kStackAnchorDelta, AsanConsts.kStackSizeForThread, AsanSizeClass.kPageSize. unfold usp in *.
    Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac lia1 H := solve [clear -H; lia].
  Ltac lia2 H1 H2 := solve [clear -H1 H2; lia].
  Ltac lia3 H1 H2 H3 := solve [clear -H1 H2 H3; lia].
  Ltac lia4 H1 H2 H3 H4 := solve [clear -H1 H2 H3 H4; lia].

  Theorem init_env0_ok : B_benv5.env0_ok5 (aenv_of hs E).
  Proof.
    pose proof R514 as R514'. pose proof R515 as R515'. pose proof R226 as R226'. pose proof R245 as R245'. pose proof R244 as R244'. pose proof R246 as R246'. pose proof R438 as R438'.
    pose proof ceil_eq as CE. pose proof pusp_le as PU. pose proof S514 as S514'. pose proof S515 as S515'. pose proof Z514 as Z514'. pose proof Z515 as Z515'.
    pose proof D226_514 as D1. pose proof D438_514 as D2. pose proof D438_515 as D3. pose proof D246_514 as D4. pose proof D246_515 as D5.
    pose proof D245_514 as D6. pose proof D244_514 as D7. pose proof stack_top_range as ST.
    unfold B_benv5.env0_ok5, BF_place.placed, AsanRep.img_sep.
    cbn [AsanState.ae_depot_nodes AsanState.ae_store_blk AsanState.ae_reserved AsanState.ae_resv_beg AsanState.ae_fs_beg AsanState.ae_fs_len
         AsanState.ae_iarena AsanState.ae_img AsanState.ae_ic AsanState.ae_thread AsanState.ae_ptr_array aenv_of A_IMG fst snd].
    unfold AsanConsts.kDepotNodeBlockBytes, AsanConsts.kStoreBlockBytes, AsanKern.kResvLen, AsanKern.kPtrArrayLen, AsanRep.kIArenaLen,
           BF_place.A_IMG_END, BF_place.A_LOWAPP_END, BF_place.A_HIGH_BEG.
    split; [unfold reserved_of; cbn [In]; inlist|]. split; [unfold reserved_of; cbn [In]; inlist|].
    split; [clear -R514' S514' Z514' CE PU; lia|]. split; [clear -R515' S515' Z515' CE PU; lia|]. split; [lia1 R514'|]. split; [lia1 R515'|].
    split; [lia1 D1|]. split; [lia1 D2|]. split; [lia1 D3|]. split; [lia1 D4|]. split; [lia1 D5|].
    split; [intros r Hr; pose proof (img_ranges_asan r Hr) as X; clear -X; tauto|].
    split; [intros r x Hr Hx; exact (proj2 (proj2 (img_ranges_asan r Hr)) x Hx)|].
    split; [unfold pgv; rewrite Z.mul_comm; apply Z_mod_mult|]. split; [unfold pgv; rewrite Z.mul_comm; apply Z_mod_mult|].
    split; [lia1 ST|]. split; [lia1 ST|]. split; [reflexivity|]. split; [lia1 D6|]. lia1 D7.
  Qed.

  (* [comment removed for export] *)
  #[local] Ltac resv_tac RR CE PU S Z I Da Db Dc Dd De :=
    unfold B_benv5.resv_range_ok, BF_place.placed_s, AsanRep.img_sep;
    cbn [AsanState.ae_depot_nodes AsanState.ae_store_blk AsanState.ae_reserved AsanState.ae_resv_beg AsanState.ae_fs_beg AsanState.ae_fs_len
         AsanState.ae_img AsanState.ae_ptr_array aenv_of A_IMG fst snd];
    unfold AsanConsts.kDepotNodeBlockBytes, AsanKern.kResvLen, AsanKern.kPtrArrayLen, BF_place.A_IMG_END, BF_place.A_LOWAPP_END, BF_place.A_HIGH_BEG;
    split; [unfold reserved_of; cbn [In]; inlist|];
    split; [split; [lia1 RR|]; split; [lia3 S CE PU|]; split; [lia1 I| lia1 Z]|];
    split; [lia1 I|]; split; [lia1 Da|]; split; [lia1 Db|]; split; [lia1 Dc|]; split; [lia1 Dd| lia1 De].
  Lemma resv_iarena : B_benv5.resv_range_ok (aenv_of hs E) (pgv E 246) 65536.
  Proof.
    pose proof R246 as RR. pose proof ceil_eq as CE. pose proof pusp_le as PU. pose proof S246 as S. pose proof Z246 as Z.
    assert (I : pgv E 246 + 65536 <= 0x10000 \/ 0x603000 <= pgv E 246) by (clear -RR; lia).
    pose proof D246_226 as Da. pose proof D246_438 as Db. pose proof D246_515 as Dc. pose proof D246_244 as Dd. pose proof D246_514 as De.
    resv_tac RR CE PU S Z I Da Db Dc Dd De.
  Qed.
  Lemma resv_dtls : B_benv5.resv_range_ok (aenv_of hs E) (pgv E 340) 4096.
  Proof.
    pose proof R340 as RR. pose proof ceil_eq as CE. pose proof pusp_le as PU. pose proof S340 as S. pose proof Z340 as Z. pose proof I340 as I.
    pose proof D340_226 as Da. pose proof D340_438 as Db. pose proof D340_515 as Dc. pose proof D340_244 as Dd. pose proof D340_514 as De.
    resv_tac RR CE PU S Z I Da Db Dc Dd De.
  Qed.
  Lemma resv_thread : B_benv5.resv_range_ok (aenv_of hs E) (pgv E 245) 4096.
  Proof.
    pose proof R245 as RR. pose proof ceil_eq as CE. pose proof pusp_le as PU. pose proof S245 as S. pose proof Z245 as Z. pose proof I245 as I.
    pose proof D226_245 as Da. pose proof D438_245 as Db. pose proof D515_245 as Dc. pose proof D245_244 as Dd. pose proof D245_514 as De.
    resv_tac RR CE PU S Z I Da Db Dc Dd De.
  Qed.

  Theorem init_pl0_ok : B_benv5.pl0_ok5 (aenv_of hs E) (plumb_of E).
  Proof.
    pose proof D246_245 as Da. pose proof D340_245 as Db. pose proof D340_246 as Dc.
    unfold B_benv5.pl0_ok5. cbn [BF_fakestack_rep.fp_ctx BF_fakestack_rep.fp_dtls AsanState.ae_thread AsanState.ae_iarena plumb_of aenv_of]. unfold AsanRep.kIArenaLen.
    split; [exists (pgv E 246), 65536; split; [exact resv_iarena | clear; lia]|].
    split; [exists (pgv E 340), 4096; split; [exact resv_dtls | clear; lia]|].
    split; [exact resv_thread|]. split; [lia1 Da|]. split; [lia1 Db|]. split; [lia1 Dc|]. clear; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_wf_env : AsanRep.wf_env (aenv_of hs E).
  Proof.
    pose proof R438 as R438'. pose proof R246 as R246'. pose proof R245 as R245'. pose proof R244 as R244'. pose proof R226 as R226'. pose proof R227 as R227'.
    pose proof ceil_eq as CE. pose proof pusp_le as PU. pose proof stack_top_range as ST. pose proof space_beg_aligned as SBA.
    pose proof S226 as S1. pose proof S438 as S2. pose proof S245 as S3. pose proof S244 as S4. pose proof S246 as S5.
    pose proof Z438 as Y1. pose proof Z245 as Y2. pose proof Z244 as Y3. pose proof Z246 as Y4. pose proof I245 as I1.
    pose proof D438_226 as D1. pose proof D226_245 as D2. pose proof D244_226 as D3. pose proof D438_245 as D4. pose proof D438_244 as D5.
    pose proof D245_244 as D6. pose proof D246_226 as D7.
    unfold AsanRep.wf_env, AsanRep.img_sep, AsanLayout.app_mem.
    cbn [AsanState.ae_space_beg AsanState.ae_resv_beg AsanState.ae_reserved AsanState.ae_ptr_array AsanState.ae_fs_beg AsanState.ae_fs_len
         AsanState.ae_thread AsanState.ae_iarena AsanState.ae_img aenv_of A_IMG fst snd].
    rewrite AsanSizeClass.kHighMemBeg_val, AsanLayout.kLowAppEnd_val. unfold AsanSizeClass.kSpaceSize, AsanRep.kIArenaLen.
    repeat match goal with |- _ /\ _ => split end.
    all: try match goal with |- In _ _ => unfold reserved_of, A_IMG; cbn [In]; inlist end.
    all: try exact SBA.
    all: try (unfold pgv; rewrite Z.mul_comm; apply Z_mod_mult).
    all: clear HC.
    all: first [ lia2 R226' R227' | lia1 ST | lia3 S1 CE PU | lia3 S2 CE PU | lia3 S3 CE PU | lia3 S4 CE PU | lia3 S5 CE PU
               | lia1 D1 | lia1 D2 | lia1 D3 | lia1 D4 | lia1 D5 | lia1 D6 | lia1 D7 | lia1 I1 | lia1 R244' | lia1 R438' | lia1 R246' | lia1 R438'
               | solve [clear -Y1 S2 CE PU R438'; lia] | solve [clear -Y2 S3 CE PU R245'; lia] | solve [clear -Y3 S4 CE PU R244'; lia] | solve [clear -Y4 S5 CE PU R246'; lia]
               | lia ].
  Qed.

End MainInit.
