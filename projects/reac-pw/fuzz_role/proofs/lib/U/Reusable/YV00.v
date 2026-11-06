From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0h YK14 YK1b YP0m YP0e YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YH00 YH03 YH02 YO0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* src0_vmlock (YH03.v) is Some v when musl's __vm_wait is the real routine: it reads the 4-byte word at v and returns
   when it is 0. The allocator invariant keeps that word 0 (statics_ok.st_vmlock), and every symbolic run that goes
   through mmap, munmap or mremap carries vml_mem, the read-only region of those 4 bytes with value 0. *)
Definition vml_region (v : Z) : region := mkRegion None v (v + 4) 0 0 [mkChunk v (CVal 4 (SLit 0))].
Definition vml_mem : smem := match src0_vmlock with Some v => [vml_region v] | None => [] end.
Definition vml_skel : list (option nat * Z * Z) := map (fun r => (r_base r, r_lo r, r_hi r)) vml_mem.
Ltac vml_case H := unfold src0_vmlock in H; first [ discriminate H | injection H as <- ].
Lemma In_vml_mem : forall r, In r vml_mem -> exists v, src0_vmlock = Some v /\ r = vml_region v.
Proof.
intros r. unfold vml_mem. destruct src0_vmlock as [v|]; intros H; [|destruct H].
destruct H as [<-|[]]. exists v. split; reflexivity.
Qed.
Lemma vml_static : forall v x, src0_vmlock = Some v -> v <= x < v + 4 -> static_owned src0_msyms x.
Proof.
intros v x Hv Hx.
assert (E1 : vml_lo src0_msyms = v) by (unfold vml_lo; cbn [ms_vmlock src0_msyms]; rewrite Hv; reflexivity).
assert (E2 : vml_len src0_msyms = 4) by (unfold vml_len; cbn [ms_vmlock src0_msyms]; rewrite Hv; reflexivity).
unfold static_owned. rewrite E1, E2. lia.
Qed.
Lemma vml_statics : forall mem,
(forall i, 0 <= i < vml_len src0_msyms -> mbyte (ms_segs src0_msyms) mem (vml_lo src0_msyms + i) = Some (Z_to_bv 8 0)) ->
forall v, src0_vmlock = Some v ->
0 <= v /\ v + 4 <= 2 ^ 64 /\ forall i, 0 <= i < 4 -> mbyte src0segs mem (v + i) = Some (Z_to_bv 8 0).
Proof.
intros mem H v Hv.
assert (E1 : vml_lo src0_msyms = v) by (unfold vml_lo; cbn [ms_vmlock src0_msyms]; rewrite Hv; reflexivity).
assert (E2 : vml_len src0_msyms = 4) by (unfold vml_len; cbn [ms_vmlock src0_msyms]; rewrite Hv; reflexivity).
rewrite E1, E2 in H. split; [|split; [|exact H]]; clear -Hv; vml_case Hv; lia.
Qed.
Lemma vml_mem_ok : forall segs E m,
(forall v, src0_vmlock = Some v ->
 0 <= v /\ v + 4 <= 2 ^ 64 /\ forall i, 0 <= i < 4 -> mbyte segs m (v + i) = Some (Z_to_bv 8 0)) ->
Forall (region_ok segs E m) vml_mem.
Proof.
intros segs E m H. unfold vml_mem. destruct src0_vmlock as [v|] eqn:Hv; [|constructor].
destruct (H v eq_refl) as (H0 & H1 & H2). constructor; [|constructor].
unfold region_ok, vml_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. intros i Hi. cbn [c_off c_val c_len cv_len] in Hi |- *.
exists (byte_of_word (sv_denot E (SLit 0)) i). split; [reflexivity|].
replace (0 + v + i) with (v + i) by lia. rewrite H2 by lia. f_equal.
unfold byte_of_word. cbn [sv_denot]. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 0) with 0. rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma all_disjoint_app : forall E r l1 l2,
all_disjoint E r l1 -> all_disjoint E r l2 -> all_disjoint E r (l1 ++ l2).
Proof.
intros E r l1 l2 H1 H2. induction l1 as [|x l1 IH]; cbn [app all_disjoint] in *; [exact H2|].
destruct H1 as [Hx H1]. split; [exact Hx | apply IH; exact H1].
Qed.
Lemma pairwise_disjoint_vml : forall E l, pairwise_disjoint E l ->
(forall v, src0_vmlock = Some v -> Forall (fun r => extent_disjoint E r (vml_region v)) l) ->
pairwise_disjoint E (l ++ vml_mem).
Proof.
intros E l Hp Hd. unfold vml_mem. destruct src0_vmlock as [v|] eqn:Hv; [|rewrite app_nil_r; exact Hp].
pose proof (Hd v eq_refl) as F. clear Hd. induction l as [|r l IH].
- cbn [app pairwise_disjoint all_disjoint]. split; exact I.
- cbn [app pairwise_disjoint] in Hp |- *. destruct Hp as [Ha Hp]. apply Forall_cons_iff in F as [Fr Fl].
split; [apply all_disjoint_app; [exact Ha | cbn [all_disjoint]; split; [exact Fr | exact I]] | apply IH; assumption].
Qed.
