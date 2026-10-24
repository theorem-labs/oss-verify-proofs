(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK0m YK14 YK1c YK1d.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section g.
Context {fx : FPState}.
Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.
Lemma with_fs_fs : forall f m, m_fs (with_fs f m) = f.
Proof. reflexivity. Qed.
Lemma with_fs_halted : forall f m, m_halted (with_fs f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fs_fds : forall f m, m_fds (with_fs f m) = m_fds m.
Proof. reflexivity. Qed.
Lemma adv_eff_ret : forall regs pc x8 mem rom r,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
intros regs pc x8 mem rom r.
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros apply_writes apply_zeros].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
Lemma adv_eff_ret_copyins : forall regs pc x8 mem rom r copyins,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
(with_copyins copyins (mkEffect r [] [])))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
intros regs pc x8 mem rom r copyins.
unfold with_copyins.
apply adv_eff_ret.
Qed.
Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8,
in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.
Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
apply path_eqb_eq in E. congruence.
Qed.
Lemma fs_lookup_set_eq : forall fs p d, fs_lookup (fs_set fs p d) p = Some d.
Proof.
induction fs as [|[q dq] fs IH]; intros p d; cbn.
- rewrite path_eqb_refl. reflexivity.
- destruct (path_ltb p q); cbn.
+ rewrite path_eqb_refl. reflexivity.
+ destruct (path_eqb p q) eqn:E; cbn.
* rewrite path_eqb_refl. reflexivity.
* rewrite E. apply IH.
Qed.
Lemma fs_lookup_set_neq : forall fs p d q, q <> p ->
fs_lookup (fs_set fs p d) q = fs_lookup fs q.
Proof.
induction fs as [|[r dr] fs IH]; intros p d q Hne; cbn.
- rewrite path_eqb_neq by exact Hne. reflexivity.
- destruct (path_ltb p r); cbn.
+ rewrite path_eqb_neq by exact Hne. reflexivity.
+ destruct (path_eqb p r) eqn:E; cbn.
* apply path_eqb_eq in E. subst r.
rewrite path_eqb_neq by exact Hne. reflexivity.
* destruct (path_eqb q r); [reflexivity | apply IH; exact Hne].
Qed.
Lemma path_ltb_irrefl : forall p, path_ltb p p = false.
Proof.
induction p as [|a p IH]; cbn; [reflexivity|].
unfold bv_ltu. rewrite Z.ltb_irrefl, bv_eqb_refl, IH. reflexivity.
Qed.
Lemma fs_set_set : forall fs p d d', fs_set (fs_set fs p d) p d' = fs_set fs p d'.
Proof.
induction fs as [|[q dq] fs IH]; intros p d d'; cbn.
- rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
- destruct (path_ltb p q) eqn:EL; cbn.
+ rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
+ destruct (path_eqb p q) eqn:EE; cbn.
* rewrite path_ltb_irrefl, path_eqb_refl. reflexivity.
* rewrite EL, EE, IH. reflexivity.
Qed.
Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
intros fds k e fd Hne. cbn.
rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.
Lemma fd_lookup_cons_None : forall fds k e fd,
fd_lookup ((k, e) :: fds) fd = None -> k <> fd /\ fd_lookup fds fd = None.
Proof.
intros fds k e fd H. cbn in H.
destruct (bv_eqb k fd) eqn:E; [discriminate|].
split; [|exact H].
intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.
Lemma fd_filter_id : forall fds fd,
fd_lookup fds fd = None ->
List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
induction fds as [|[k e] fds IH]; intros fd H; [reflexivity|].
apply fd_lookup_cons_None in H. destruct H as [Hne H].
cbn [List.filter fst]. rewrite (bv_eqb_neq k fd Hne). cbn [negb].
rewrite IH by exact H. reflexivity.
Qed.
Lemma fd_insert_fresh : forall fds fd e,
fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof.
intros fds fd e H. unfold fd_insert. rewrite fd_filter_id by exact H.
reflexivity.
Qed.
Lemma fd_lookup_filter_neq : forall fds fd fd', fd' <> fd ->
fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) fd' = fd_lookup fds fd'.
Proof.
induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
cbn [List.filter fst].
destruct (bv_eqb k fd) eqn:Hk.
- apply bv_eqb_eq in Hk. subst k.
cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
rewrite bv_eqb_neq by congruence. reflexivity.
- cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.
Lemma fd_lookup_insert_eq : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.
Lemma fd_lookup_insert_neq : forall fds fd e fd', fd' <> fd ->
fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd'.
Proof.
intros fds fd e fd' Hne. unfold fd_insert.
rewrite fd_lookup_cons_neq by congruence.
apply fd_lookup_filter_neq. exact Hne.
Qed.
Lemma fd_lookup_remove_neq : forall fds fd fd', fd' <> fd ->
fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd'.
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.
Lemma fd_lookup_some_none_neq : forall fds a b ea,
fd_lookup fds a = Some ea -> fd_lookup fds b = None -> a <> b.
Proof. intros fds a b ea Ha Hb ->. congruence. Qed.
Lemma free_fd_after_open : forall x y z fdin e,
exists w, fd_lookup (fd_insert
[(Z_to_bv 64 0, x); (Z_to_bv 64 1, y); (Z_to_bv 64 2, z)] fdin e) w = None
/\ (bv_unsigned w < 2 ^ 31)%Z.
Proof.
intros x y z fdin e.
destruct (decide (fdin = Z_to_bv 64 3)) as [->|Hne].
- exists (Z_to_bv 64 4). split.
+ rewrite fd_lookup_insert_neq
by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
reflexivity.
+ change (bv_unsigned (Z_to_bv 64 4)) with 4%Z. lia.
- exists (Z_to_bv 64 3). split.
+ rewrite fd_lookup_insert_neq by congruence. reflexivity.
+ change (bv_unsigned (Z_to_bv 64 3)) with 3%Z. lia.
Qed.
Lemma filter_fd_cons_keep : forall {B} (fds : list (word * B)) k (e : B) fd,
k <> fd ->
List.filter (fun p => negb (bv_eqb (fst p) fd)) ((k, e) :: fds)
= (k, e) :: List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
intros B fds k e fd Hne. cbn [List.filter fst].
rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.
Lemma filter_fd_cons_drop : forall {B} (fds : list (word * B)) fd (e : B),
List.filter (fun p => negb (bv_eqb (fst p) fd)) ((fd, e) :: fds)
= List.filter (fun p => negb (bv_eqb (fst p) fd)) fds.
Proof.
intros B fds fd e. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma length_file_read : forall data off count,
length (file_read data off count)
= Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
intros data off count. rewrite file_read_unguarded.
rewrite length_firstn, length_skipn. reflexivity.
Qed.
Lemma file_read_nil : forall data off count,
(length data <= word_to_nat off)%nat -> file_read data off count = [].
Proof.
intros data off count H. rewrite file_read_unguarded.
rewrite skipn_all2 by exact H. apply firstn_nil.
Qed.
Lemma file_write_append : forall data off bs,
word_to_nat off = length data -> file_write data off bs = data ++ bs.
Proof.
intros data off bs Hoff. unfold file_write.
destruct bs as [|b bs]; [now rewrite app_nil_r|]. cbv zeta.
rewrite Hoff, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
rewrite firstn_all.
rewrite skipn_all2 by lia.
rewrite app_nil_r. reflexivity.
Qed.
Lemma firstn_add {A} : forall (l : list A) n m,
firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
induction l as [|x l IH]; intros n m.
- rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
- destruct n as [|n]; [reflexivity|].
cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.
Lemma copy_step : forall data (off count : word),
firstn (word_to_nat off) data ++ file_read data off count
= firstn (word_to_nat off
+ Nat.min (word_to_nat count) (length data - word_to_nat off)) data.
Proof.
intros data off count. rewrite file_read_unguarded.
rewrite firstn_add. f_equal.
destruct (Nat.le_ge_cases (word_to_nat count)
(length data - word_to_nat off)) as [H|H].
- rewrite Nat.min_l by exact H. reflexivity.
- rewrite Nat.min_r by exact H.
rewrite firstn_all2 by (rewrite length_skipn; lia).
rewrite firstn_all2 by (rewrite length_skipn; lia).
reflexivity.
Qed.
Definition mrb (segs : list Segment) (mem : word -> option byte)
: word -> option byte :=
fun a => match mem a with Some b => Some b | None => seg_rom segs a end.
Lemma ms_read_byte_mrb : forall segs regs pc mem,
ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem.
Proof. reflexivity. Qed.
Lemma ms_read_byte_rec_mrb : forall segs regs fr pc sv rv fc mem,
ms_read_byte {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := seg_rom segs |}
= mrb segs mem.
Proof. reflexivity. Qed.
Lemma mrb_first : forall segs mem a n b rest,
rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
as [b1|]; [|discriminate].
destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
injection H; intros; subst; congruence.
Qed.
Lemma rdn_tail : forall segs mem a n b rest,
rdn segs mem a (S n) = Some (b :: rest) -> rdn segs mem (a + 1) n = Some rest.
Proof.
intros segs mem a n b rest H. cbn [rdn] in H.
destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
as [b1|]; [|discriminate].
destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
injection H; intros; subst; reflexivity.
Qed.
Lemma read_cstr_aux_of_rdn : forall segs str fuel mem a,
(length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
read_cstr_aux (mrb segs mem) a fuel = CstrOk str.
Proof.
intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
- cbn [length] in *. destruct fuel as [|fuel]; [lia|].
assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
cbn [read_cstr_aux]. rewrite Hb0. reflexivity.
- cbn [length] in *. destruct fuel as [|fuel]; [lia|].
cbn [read_cstr_aux]. cbn [app] in Hr.
assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
assert (Hfirst : mrb segs mem a = Some b)
by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
exact Hr).
assert (Htail : rdn segs mem (a + 1) (length str + 1)
= Some (str ++ [Z_to_bv 8 0]))
by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
exact Hr).
rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
rewrite (IH fuel mem (a + 1) ltac:(lia)
ltac:(intro; apply Hnz; right; assumption) Htail).
reflexivity.
Qed.
Lemma read_cstr_of_rdn : forall segs mem a str,
(length str <= 4095)%nat -> ~ In (Z_to_bv 8 0) str ->
rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
read_cstr (mrb segs mem) a = CstrOk str.
Proof.
intros segs mem a str Hlen Hnz Hr.
unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hr].
change path_max with 4096%nat. lia.
Qed.
Lemma read_cstr_aux_toolong_of_rdn : forall segs fuel bs mem a,
length bs = fuel -> ~ In (Z_to_bv 8 0) bs ->
rdn segs mem a fuel = Some bs ->
read_cstr_aux (mrb segs mem) a fuel = CstrTooLong.
Proof.
intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hr;
[reflexivity|].
destruct bs as [|b bs]; [cbn in Hlen; lia|].
cbn [read_cstr_aux].
assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
assert (Hfirst : mrb segs mem a = Some b)
by (apply (mrb_first segs mem a fuel b bs); exact Hr).
assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
ltac:(intro; apply Hnz; right; assumption) Htail).
reflexivity.
Qed.
Lemma read_cstr_toolong_of_rdn : forall segs mem a bs,
length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs ->
rdn segs mem a 4096%nat = Some bs ->
read_cstr (mrb segs mem) a = CstrTooLong.
Proof.
intros segs mem a bs Hlen Hnz Hr.
unfold read_cstr. change path_max with 4096%nat.
eapply read_cstr_aux_toolong_of_rdn; eauto.
Qed.
Lemma read_argv_cstr_k : forall ph segs (sp : word) av ev k uid hw rnd,
(k < length av)%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
(cat_argv_ptr sp av ev k) (length (nth k av []) + 1)
= Some (nth k av [] ++ [Z_to_bv 8 0]).
Proof.
intros ph segs sp av ev k uid hw rnd Hk Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (nth k av [] ++ [Z_to_bv 8 0]) post (length (nth k av []) + 1)) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [exact E | | exact Hnw].
rewrite length_app. cbn [length]. lia.
Qed.
Lemma read_argv_prefix_k : forall ph segs (sp : word) av ev k n uid hw rnd,
(k < length av)%nat -> (n <= length (nth k av []))%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
(cat_argv_ptr sp av ev k) n
= Some (firstn n (nth k av [])).
Proof.
intros ph segs sp av ev k n uid hw rnd Hk Hn Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (firstn n (nth k av []))
((skipn n (nth k av []) ++ [Z_to_bv 8 0]) ++ post) n) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [| |exact Hnw].
- rewrite E. rewrite <- !app_assoc.
rewrite (app_assoc (firstn n (nth k av [])) (skipn n (nth k av []))).
rewrite firstn_skipn. reflexivity.
- apply firstn_length_le. exact Hn.
Qed.
Definition fout_trace (o : word * Fs.Fs) : list event := [ExitEv (fst o) (snd o)].
Section h.
Variable segs : list Segment.
Inductive to_fout : machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfo_exit : forall ms model x8 (U : (word * Fs.Fs) -> Prop),
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
(forall o, U o <-> o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) ->
to_fout ms model U
| tfo_step : forall ms ms' model U,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_fout ms' model U ->
to_fout ms model U
| tfo_sys : forall ms model x8
(T : SyscallEffect -> Model -> (word * Fs.Fs) -> Prop)
(U : (word * Fs.Fs) -> Prop),
ms_svc_pending ms = Some x8 ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) ->
(forall eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
(forall eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
to_fout (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
(forall o, U o <->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
/\ T eff model' o)) ->
to_fout ms model U.
Lemma tfo_msteps : forall ms ms' model U,
msteps segs ms ms' -> to_fout ms' model U -> to_fout ms model U.
Proof.
intros ms ms' model U H; induction H; [auto|].
intro Ht. eapply tfo_step; eauto.
Qed.
Lemma tfo_equiv : forall ms model U V,
to_fout ms model U ->
(forall o, V o <-> U o) ->
to_fout ms model V.
Proof.
intros ms model U V Hto; revert V.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros V HV.
- apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
intro o. rewrite (HV o). apply HU.
- eapply tfo_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
- apply (tfo_sys ms model x8 T V);
[exact Hsvc | exact Hne | exact Hrec | exact Hshape | exact Hcont |].
intro o. rewrite (HV o). apply HU.
Qed.
Lemma to_fout_nonempty : forall ms model U,
to_fout ms model U -> exists o, U o.
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ].
- exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
apply HU. reflexivity.
- exact IH.
- destruct Hrec as (eff & model' & evs & Hspec).
destruct (IH eff model' evs Hspec) as [o Ho].
exists o. apply HU. exists eff, model', evs. auto.
Qed.
Lemma sstep_fsys_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
(forall eff model' evs',
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs') ->
evs' = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
sstep segs (mkCfg ms model) evs st ->
exists eff model',
syscall_spec (sys_input segs ms x8) model (Ok eff model' []) /\
evs = [] /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (He & _ & Hlazy');
subst evs0;
match goal with
| Hmat : materialize_model_accesses model' _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
inversion Hmat; subst model''
end;
exists eff, model'; auto
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & _ & Hlazy');
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy') in Hmat;
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
congruence
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (Hshape eff model' evs0 H3) as (_ & Hm & _);
assert (Hhn : m_halted model' = None) by congruence;
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
end.
Qed.
Definition fout_post (U : (word * Fs.Fs) -> Prop) : post :=
fun tr o => exists out, U out /\ tr = fout_trace out /\ exits_with (fst out) tr o.
Lemma to_fout_exec : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
OmniRun.exec segs (mkCfg ms model) (fout_post U).
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros Hh Hlazy.
-
apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_si. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold fout_post. cbn beta.
exists (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model).
split; [apply HU; reflexivity |].
split; [unfold fout_trace; cbn [fst snd app]; reflexivity |].
cbn [exits_with cfg_model fst]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
-
apply exec_step; [exact Hh | | |].
+ destruct Hrec as (eff & model' & evs & Hspec).
destruct (Hshape eff model' evs Hspec) as (-> & Hh' & Hlazy').
eexists; eexists.
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
+ intros evs Hss.
destruct (sstep_fsys_inv ms model x8 evs SError Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & _ & _ & Habs). discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_fsys_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' Hlazy') |].
intros tr o (out & Hout & Heq & Hx). exists out.
split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
split; [cbn [app]; exact Heq | exact Hx].
Qed.
Lemma to_fout_star_only : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
forall tr c, star segs (mkCfg ms model) tr c ->
exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
intros ms model U Hto Hh Hlazy tr c Hstar.
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_fout_exec ms model U Hto Hh Hlazy) Hstar))
as (tr' & o & _ & (out & Hout & Heq & _)).
exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.
Lemma to_fout_star_admits : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
forall o, U o ->
exists c, star segs (mkCfg ms model) (fout_trace o) c.
Proof.
intros ms model U Hto.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros Hh Hlazy o Ho.
-
apply HU in Ho. subst o. unfold fout_trace; cbn [fst snd].
exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
apply star_one.
replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
+ exact Hh.
+ exact Hsvc.
+ apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_si. exact Hx8.
+ cbn. reflexivity.
+ apply m_killed_with_halted.
-
destruct (IH Hh Hlazy o Ho) as [c Hstar].
exists c.
replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
eapply star_step; [|exact Hstar].
apply (sstep_instr segs ms model ms' model); try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
-
apply HU in Ho.
destruct Ho as (eff & model' & evs & Hspec & Ht).
destruct (Hshape eff model' evs Hspec) as (He & Hh' & Hlazy'). subst evs.
destruct (IH eff model' [] Hspec Hh' Hlazy' o Ht) as [c Hstar].
exists c.
replace (fout_trace o) with ([] ++ fout_trace o) by reflexivity.
eapply star_step; [|exact Hstar].
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy'). reflexivity.
Qed.
Lemma to_fout_progress : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
forall evs st, sstep segs (mkCfg ms model) evs st ->
exists ms' model', st = SNext (mkCfg ms' model') /\
(m_halted model' <> None \/
(m_halted model' = None /\ m_vm_lazy model' = [] /\
exists U', to_fout ms' model' U')).
Proof.
intros ms model U Hto Hh Hlazy evs st Hss.
revert evs st Hss.
induction Hto as
[ ms model x8 U Hsvc Hx8 HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hne Hrec Hshape Hcont IH HU ];
intros evs st Hss.
-
destruct (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss)
as [_ Hst]. subst st.
do 2 eexists. split; [reflexivity|]. left. cbn. discriminate.
-
destruct (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss)
as [_ Hst]. subst st.
do 2 eexists. split; [reflexivity|]. right.
repeat split; try assumption. exists U. exact Hto.
-
destruct (sstep_fsys_inv ms model x8 evs st Hh Hlazy Hsvc Hne Hshape Hss)
as (eff & model' & Hspec & _ & Hst). subst st.
destruct (Hshape eff model' [] Hspec) as (_ & Hh' & Hlazy').
do 2 eexists. split; [reflexivity|]. right.
repeat split; try assumption.
exists (T eff model'). exact (Hcont eff model' [] Hspec).
Qed.
Definition fon_path (c : config) : Prop :=
(m_halted (cfg_model c) = None
/\ m_vm_lazy (cfg_model c) = []
/\ exists U, to_fout (cfg_ms c) (cfg_model c) U)
\/ m_halted (cfg_model c) <> None.
Lemma fon_path_step : forall c evs c',
fon_path c -> sstep segs c evs (SNext c') -> fon_path c'.
Proof.
intros [ms model] evs [ms' model'] Hop Hss.
unfold fon_path in *; cbn in Hop |- *.
destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
- destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
as (ms'' & model'' & Hst & Hcase).
inversion Hst; subst.
destruct Hcase as [Hhz | (Hhz & Hlazy' & U' & Hto')].
+ right. exact Hhz.
+ left. repeat split; try assumption. exists U'; exact Hto'.
- exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma fon_path_no_error : forall c evs, fon_path c -> ~ sstep segs c evs SError.
Proof.
intros [ms model] evs Hop Hss.
unfold fon_path in Hop; cbn in Hop.
destruct Hop as [(Hh & Hlazy & U & Hto) | Hh].
- destruct (to_fout_progress ms model U Hto Hh Hlazy evs _ Hss)
as (ms'' & model'' & Hst & _). discriminate.
- inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma star_fon_path : forall c tr c',
fon_path c -> star segs c tr c' -> fon_path c'.
Proof. exact (star_inv segs fon_path fon_path_step). Qed.
Lemma to_fout_no_error : forall ms model U,
to_fout ms model U ->
m_halted model = None ->
m_vm_lazy model = [] ->
~ reaches_error segs (mkCfg ms model).
Proof.
intros ms model U Hto Hh Hlazy. apply exec_no_error.
eapply exec_conseq; [exact (to_fout_exec ms model U Hto Hh Hlazy) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma star_syscall_nil : forall ms model x8 eff model',
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
m_halted model' = None ->
m_vm_lazy model' = [] ->
star segs (mkCfg ms model) []
(mkCfg (advance_past_svc (apply_effect ms eff)) model').
Proof.
intros ms model x8 eff model' Hh Hsvc Hspec Hh' Hlazy.
apply star_one.
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy model' _ Hlazy). reflexivity.
Qed.
Lemma reaches_error_star : forall c tr c',
star segs c tr c' -> reaches_error segs c' -> reaches_error segs c.
Proof.
intros c tr c' Hstar (tr2 & c2 & evs & Hstar2 & Hss).
exists (tr ++ tr2), c2, evs. split; [eapply star_trans; eauto | exact Hss].
Qed.
Lemma spec_err_error : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model Unmodeled ->
reaches_error segs (mkCfg ms model).
Proof.
intros ms model x8 Hh Hsvc Hspec.
exists [], (mkCfg ms model), []. split; [apply star_refl|].
eapply sstep_syscall_unmodeled; eassumption.
Qed.
Lemma msteps_spec_err_error : forall ms ms' model x8,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = Some x8 ->
syscall_spec (sys_input segs ms' x8) model Unmodeled ->
reaches_error segs (mkCfg ms model).
Proof.
intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
eapply reaches_error_star.
- apply msteps_star_nil; eassumption.
- eapply spec_err_error; eassumption.
Qed.
Lemma spec_err_all_traces_error : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model Unmodeled ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms model x8 Hh Hsvc Hspec.
assert (Hno_ok : forall eff model' events,
~ syscall_spec (sys_input segs ms x8) model
(Ok eff model' events)).
{ intros eff model' events Hok.
pose proof Hspec as Herr.
apply (check_syscall_complete_unmodeled _ _ eff) in Herr.
apply check_syscall_complete_ok in Hok.
rewrite Herr in Hok. discriminate Hok. }
constructor.
- exists [], SError. eapply sstep_syscall_unmodeled; eassumption.
- intros evs c' Hnext. inversion Hnext; subst; try congruence.
all: exfalso;
match goal with
| Hno : forall (eff0 : SyscallEffect) (model0 : Model)
(events0 : list event),
~ syscall_spec (sys_input ?segs0 ?ms0 ?expected) ?m0
(Ok eff0 model0 events0),
Hexpected : ms_svc_pending ?ms0 = Some ?expected,
Hactual : ms_svc_pending ?ms0 = Some ?actual,
Hok : syscall_spec (sys_input ?segs0 ?ms0 ?actual) ?m0
(Ok ?eff ?model' ?events) |- _ =>
assert (actual = expected) by congruence; subst actual;
exact (Hno eff model' events Hok)
end.
Qed.
Lemma msteps_spec_err_all_traces_error : forall ms ms' model x8,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = Some x8 ->
syscall_spec (sys_input segs ms' x8) model Unmodeled ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms ms' model x8 Hh Hlazy Hm Hsvc Hspec.
eapply msteps_all_traces_error; [exact Hh | exact Hlazy | exact Hm |].
eapply spec_err_all_traces_error; eassumption.
Qed.
Lemma tfo_exit_code : forall ms model x8 code,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
ms_gpr ms 0 = code ->
bv_and code (Z_to_bv 64 255) = code ->
to_fout ms model (fun o => o = (code, m_fs model)).
Proof.
intros ms model x8 code Hsvc Hx8 Hg Hland.
apply (tfo_exit ms model x8); [exact Hsvc | exact Hx8 |].
intro o. rewrite Hg, Hland. tauto.
Qed.
Lemma tfo_sys_det : forall ms model x8 eff model' U,
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
(forall eff2 m2 evs2,
syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) ->
eff2 = eff /\ m2 = model' /\ evs2 = []) ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
m_halted model' = None ->
m_vm_lazy model' = [] ->
to_fout (advance_past_svc (apply_effect ms eff)) model' U ->
to_fout ms model U.
Proof.
intros ms model x8 eff model' U Hsvc Hok Huniq Hne Hh' Hlazy' Hcont.
apply (tfo_sys ms model x8 (fun _ _ => U) U); [exact Hsvc | exact Hne | | | |].
- exists eff, model', []. exact Hok.
- intros eff2 m2 evs2 Hs.
destruct (Huniq eff2 m2 evs2 Hs) as (_ & -> & ->).
repeat split; assumption.
- intros eff2 m2 evs2 Hs.
destruct (Huniq eff2 m2 evs2 Hs) as (-> & -> & _). exact Hcont.
- intro o. split.
+ intro Ho. exists eff, model', []. auto.
+ intros (e2 & m2 & ev2 & _ & Ht). exact Ht.
Qed.
End h.
Lemma check_syscall_56 : forall segs ms x8 eff m,
bv_unsigned x8 = 56%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
(ms_gpr ms 2) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma check_syscall_57 : forall segs ms x8 eff m,
bv_unsigned x8 = 57%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_close (fd32 (ms_gpr ms 0)) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma check_syscall_63 : forall segs ms x8 eff m,
bv_unsigned x8 = 63%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
(ms_gpr ms 2) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma check_syscall_64 : forall segs ms x8 eff m,
bv_unsigned x8 = 64%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
(ms_gpr ms 2) eff m.
Proof.
intros segs ms x8 eff m Hno.
unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.
Lemma fd_not_error : forall fd : word,
(bv_unsigned fd < 2 ^ 31)%Z -> addr_is_error_b fd = false.
Proof.
intros fd H. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. lia.
Qed.
Lemma errno_ret_recover : forall e,
(1 <= e)%Z -> (e <= 4095)%Z ->
(two_pow_64 - bv_unsigned (errno_ret e))%Z = e.
Proof.
intros e H1 H2. rewrite (errno_ret_unsigned e H1 H2). lia.
Qed.
Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.
Lemma openat_errno_range : forall e,
In e openat_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range openat_errnos e eq_refl HIn). Qed.
Lemma check_open_result_never_unmodeled : forall eff m mk,
check_open_result eff m mk <> CheckUnmodeled.
Proof.
intros [ret ws zs us cs copyins] m mk.
unfold check_open_result, check_new_fd_result.
destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
destruct cs as [|? ?];
destruct copyins as [|? ?];
try discriminate.
destruct (errno_ret_in openat_errnos ret); [discriminate|].
destruct (fd_lookup (m_fds m) ret); [discriminate|].
destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.
Lemma check_open_result_ok_iff : forall eff m (mk : word -> Model) m' evs,
check_open_result eff m mk = CheckOk m' evs <->
((exists e, In e openat_errnos /\ eff = mkEffect (errno_ret e) [] []
/\ m' = m /\ evs = [])
\/ (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m)
/\ eff = mkEffect fd [] [] /\ m' = mk fd /\ evs = [])).
Proof.
intros [ret ws zs us cs copyins] m mk m' evs.
unfold check_open_result, check_new_fd_result. split.
- intro H.
destruct ws as [|? ?]; [|discriminate].
destruct zs as [|? ?]; [|discriminate].
destruct us as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (errno_ret_in openat_errnos ret) eqn:Herr; try rewrite Herr in H.
+ inversion H; subst.
apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
left. exists e. auto.
+ destruct (fd_lookup (m_fds m) ret) eqn:Hlk; try rewrite Hlk in H;
[discriminate|].
destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; try rewrite Heq in H;
[|discriminate].
inversion H; subst.
right. exists ret. apply bv_eqb_eq in Heq. auto.
- intros [ (e & HIn & Heff & -> & ->)
| (fd & Hlk & Heq & Heff & -> & ->) ].
+ inversion Heff; subst.
rewrite (errno_ret_in_intro _ e HIn). reflexivity.
+ inversion Heff; subst.
rewrite errno_ret_in_alloc_fd by reflexivity.
rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.
Definition open_copyins (ms : machine_state) : list (word * nat) :=
[(ms_gpr ms 1,
cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].
Definition check_open_result_copyins (reads : list (word * nat))
(eff : SyscallEffect) (m : Model) (mk : word -> Model) : check_result :=
check_copyins reads eff (check_open_result (clear_copyins eff) m mk).
Lemma effect_from_copyins_and_clear : forall eff reads core,
eff_copyins eff = reads -> clear_copyins eff = core ->
eff = with_copyins reads core.
Proof.
intros [ret ws zs us cs copyins] reads core Hreads Hcore.
cbn [eff_copyins] in Hreads. subst copyins.
unfold clear_copyins, with_copyins in Hcore |- *.
cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies] in Hcore |- *.
inversion Hcore. reflexivity.
Qed.
Lemma check_open_result_copyins_never_unmodeled : forall reads eff m mk,
check_open_result_copyins reads eff m mk <> CheckUnmodeled.
Proof.
intros reads eff m mk.
unfold check_open_result_copyins, check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads);
[apply check_open_result_never_unmodeled|discriminate].
Qed.
Lemma check_open_result_copyins_ok_iff :
forall reads eff m (mk : word -> Model) m' evs,
check_open_result_copyins reads eff m mk = CheckOk m' evs <->
((exists e, In e openat_errnos /\
eff = with_copyins reads (mkEffect (errno_ret e) [] []) /\
m' = m /\ evs = [])
\/ (exists fd, fd_lookup (m_fds m) fd = None /\
fd = alloc_fd (m_fds m) /\
eff = with_copyins reads (mkEffect fd [] []) /\
m' = mk fd /\ evs = [])).
Proof.
intros reads eff m mk m' evs.
unfold check_open_result_copyins, check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
- apply access_ranges_eqb_eq in Hreads.
rewrite check_open_result_ok_iff. split.
+ intros [(e & HIn & Hcore & -> & ->)
| (fd & Hlk & Heq & Hcore & -> & ->)].
* left. exists e. repeat split; try assumption.
eapply effect_from_copyins_and_clear; eassumption.
* right. exists fd. repeat split; try assumption.
eapply effect_from_copyins_and_clear; eassumption.
+ intros [(e & HIn & Heff & -> & ->)
| (fd & Hlk & Heq & Heff & -> & ->)].
* left. exists e. repeat split; try assumption.
rewrite Heff. reflexivity.
* right. exists fd. repeat split; try assumption.
rewrite Heff. reflexivity.
- split; [discriminate|].
intros [(e & _ & Heff & _)
| (fd & _ & _ & Heff & _)].
all: rewrite Heff in Hreads; cbn [eff_copyins with_copyins] in Hreads;
pose proof (proj2 (access_ranges_eqb_eq reads reads) eq_refl) as Htrue;
congruence.
Qed.
Lemma check_copyins_after_ret_only : forall reads eff r m evs,
Prelude.check_copyins_after reads eff
(check_ret_only (clear_copyins eff) r m evs) =
check_ret_only_copyins reads eff r m evs.
Proof.
intros reads eff r m evs.
unfold Prelude.check_copyins_after, check_ret_only_copyins.
destruct (check_ret_only (clear_copyins eff) r m evs) eqn:Hresult.
- reflexivity.
- unfold check_copyins.
destruct (access_ranges_eqb (eff_copyins eff) reads); reflexivity.
- exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.
Lemma openat_rd_check : forall segs ms x8 model p d,
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
path_eqb p [] = false ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins (open_copyins ms) eff model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFile p (Z_to_bv 64 0))) model).
Proof.
intros segs ms x8 model p d Hno Hdirfd Hpath Hpe Hfl Hdot Hfs eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl, Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_read.
rewrite ?Hdot, ?Hfs.
unfold check_open_result_copyins, open_copyins.
destruct (check_open_result (clear_copyins eff) model
(fun fd : word =>
with_fds
(fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model))
eqn:Hresult.
- reflexivity.
- reflexivity.
- exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.
Lemma openat_wr_check : forall segs ms x8 model p,
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
path_eqb p [] = false ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags ->
openat_plain_name p = true ->
fs_under (m_fs model) p = false ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins (open_copyins ms) eff model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)).
Proof.
intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl.
change (wr_create_flags =? 0)%Z with false. cbv beta iota.
rewrite Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_create, check_create_wronly.
rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
unfold check_open_result_copyins, open_copyins.
destruct (check_open_result (clear_copyins eff) model
(fun fd : word =>
with_fds
(fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)))
eqn:Hresult.
- reflexivity.
- reflexivity.
- exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.
Lemma openat_wr_isdir_check : forall segs ms x8 model p,
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
path_eqb p [] = false ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags ->
openat_plain_name p = true ->
fs_under (m_fs model) p = true ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret EISDIR) model [].
Proof.
intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hun eff.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
rewrite Hpe. cbv beta iota.
rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl.
change (wr_create_flags =? 0)%Z with false. cbv beta iota.
rewrite Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_create.
rewrite Hdot, Hun. rewrite orb_false_l. cbv beta iota.
apply check_copyins_after_ret_only.
Qed.
Lemma openat_toolong_check : forall segs ms x8 model,
bv_unsigned x8 = 56%Z ->
modeled_open_flags (ms_gpr ms 2) = true ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret ENAMETOOLONG) model [].
Proof.
intros segs ms x8 model Hno Hfl Hpath eff.
rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
rewrite Hfl. cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath.
unfold check_ret_only_copyins, open_copyins.
destruct (check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG)
model []) eqn:Hresult.
- reflexivity.
- unfold check_copyins.
destruct (access_ranges_eqb (eff_copyins eff)
[(ms_gpr ms 1,
cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]);
reflexivity.
- exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.
Section i.
Variable segs : list Segment.
Lemma tfo_open_core : forall ms model (mk : word -> Model) x8 reads
(Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
ms_svc_pending ms = Some x8 ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins reads eff model mk) ->
(forall fd, m_halted (mk fd) = None /\ m_vm_lazy (mk fd) = []) ->
(forall e, In e openat_errnos ->
to_fout segs (advance_past_svc
(apply_effect ms
(with_copyins reads (mkEffect (errno_ret e) [] []))))
model (Te e)) ->
(forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
to_fout segs (advance_past_svc
(apply_effect ms (with_copyins reads (mkEffect fd [] []))))
(mk fd) (Ts fd)) ->
(forall o, U o <->
((exists e, In e openat_errnos /\ Te e o)
\/ (exists fd, fd_lookup (m_fds model) fd = None
/\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
to_fout segs ms model U.
Proof.
intros ms model mk x8 reads Te Ts U Hsvc Hh Hlazy Hchk Hmk Herr Hok HU.
apply (tfo_sys segs ms model x8
(fun eff model' =>
if addr_is_error_b (eff_ret eff)
then Te ((two_pow_64 - bv_unsigned (eff_ret eff))%Z)
else Ts (eff_ret eff)) U); [exact Hsvc | | | | |].
-
intro Hspec.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
rewrite Hchk in Hspec.
exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hspec).
-
exists (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])), model, [].
apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. left. exists ENOMEM.
repeat split; try reflexivity. apply ENOMEM_in_openat_errnos.
-
intros eff model' evs Hspec.
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & _ & -> & -> & ->)
| (fd & _ & _ & -> & -> & ->) ].
+ repeat split; assumption.
+ destruct (Hmk fd) as [Hhalt Hlazy']. repeat split; assumption.
-
intros eff model' evs Hspec.
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & HIn & -> & -> & _)
| (fd & Hlk & Heq & -> & -> & _) ].
+ destruct (openat_errno_range e HIn) as [He1 He2].
cbn [eff_ret with_copyins].
rewrite (errno_ret_error_b e He1 He2).
rewrite (errno_ret_recover e He1 He2).
apply Herr; assumption.
+ cbn [eff_ret with_copyins].
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne.
apply Hok; assumption.
-
intro o. rewrite HU. split.
+ intros [ (e & HIn & Ht) | (fd & Hlk & Heq & Ht) ].
* destruct (openat_errno_range e HIn) as [He1 He2].
exists (with_copyins reads (mkEffect (errno_ret e) [] [])), model, [].
split.
{ apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. left. exists e. auto. }
{ cbn [eff_ret with_copyins]. rewrite (errno_ret_error_b e He1 He2).
rewrite (errno_ret_recover e He1 He2). exact Ht. }
* exists (with_copyins reads (mkEffect fd [] [])), (mk fd), [].
split.
{ apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. right. exists fd. auto. }
{ cbn [eff_ret with_copyins].
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne. exact Ht. }
+ intros (eff & model' & evs & Hspec & Ht).
apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
apply check_open_result_copyins_ok_iff in Hspec.
destruct Hspec as [ (e & HIn & -> & -> & _)
| (fd & Hlk & Heq & -> & -> & _) ].
* destruct (openat_errno_range e HIn) as [He1 He2].
cbn [eff_ret with_copyins] in Ht.
rewrite (errno_ret_error_b e He1 He2) in Ht.
rewrite (errno_ret_recover e He1 He2) in Ht.
left. exists e. auto.
* cbn [eff_ret with_copyins] in Ht.
assert (Hne : addr_is_error_b fd = false)
by (rewrite Heq; apply alloc_fd_not_error_b).
rewrite Hne in Ht.
right. exists fd. auto.
Qed.
Lemma open_ok_fd : forall ms model (mk : word -> Model) x8 reads fd,
(forall eff, check_syscall (sys_input segs ms x8) eff model
= check_open_result_copyins reads eff model mk) ->
fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
syscall_spec (sys_input segs ms x8) model
(Ok (with_copyins reads (mkEffect fd [] [])) (mk fd) []).
Proof.
intros ms model mk x8 reads fd Hchk Hlk Hlt.
apply check_syscall_ok_iff. rewrite Hchk.
apply check_open_result_copyins_ok_iff. right. exists fd. auto.
Qed.
Lemma tfo_openat_toolong : forall ms model x8 U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 56%Z ->
modeled_open_flags (ms_gpr ms 2) = true ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (advance_past_svc
(apply_effect ms
(with_copyins (open_copyins ms)
(mkEffect (errno_ret ENAMETOOLONG) [] []))))
model U ->
to_fout segs ms model U.
Proof.
intros ms model x8 U Hsvc Hno Hfl Hpath Hh Hlazy Hcont.
pose proof (openat_toolong_check segs ms x8 model Hno Hfl Hpath) as Hchk.
apply (tfo_sys_det segs ms model x8
(with_copyins (open_copyins ms)
(mkEffect (errno_ret ENAMETOOLONG) [] [])) model U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.
Lemma tfo_openat_enoent : forall ms model x8 p U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 56%Z ->
ms_gpr ms 0 = AT_FDCWD ->
read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = None ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (advance_past_svc
(apply_effect ms
(with_copyins (open_copyins ms)
(mkEffect (errno_ret ENOENT) [] []))))
model U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p U Hsvc Hno Hdirfd Hpath Hfl Hdot Hfs Hh Hlazy Hcont.
pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
apply openat_plain_name_nodirref in Hdot.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret ENOENT) model []).
{ intro eff. rewrite (check_syscall_56 segs ms x8 eff model Hno).
unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite in_mem_si, Hpath. cbv beta iota zeta.
destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
- apply check_copyins_after_ret_only.
- rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
rewrite Hunw. cbv beta iota.
rewrite Hfl, Z.eqb_refl. cbv beta iota.
unfold Open.check_openat_read. rewrite Hdot, Hfs.
apply check_copyins_after_ret_only. }
apply (tfo_sys_det segs ms model x8
(with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] []))
model U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.
Lemma tfo_read_file : forall ms model x8 p off data w U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFile p off) ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
fs_lookup (m_fs model) p = Some data ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some w ->
(bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
(0 < bv_unsigned (ms_gpr ms 2))%Z ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms
(mkEffect (len_word (file_read data off (ms_gpr ms 2)))
(delivered_writes (ms_gpr ms 1)
(file_read data off (ms_gpr ms 2))) [])))
(with_fds
(fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word (file_read data off (ms_gpr ms 2)))))
model)
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p off data w U Hsvc Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok Hh Hlazy Hcont.
set (bs := file_read data off (ms_gpr ms 2)).
assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
<= bv_unsigned (ms_gpr ms 2))%Z).
{ unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (u64_range (ms_gpr ms 2)) as Hc.
rewrite length_file_read, Nat2Z.inj_min.
unfold word_to_nat.
rewrite Z.mod_small; lia. }
assert (Hchk : forall eff m' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
(eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
/\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word bs))) model
/\ evs = [])).
{ intros eff m' evs.
rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite Haok. cbn [negb]. cbv beta iota.
rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
rewrite Hfs. cbv beta iota zeta.
rewrite in_wmem_si.
rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
unfold bs.
destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
-
cbv beta iota.
rewrite check_ret_only_ok_iff. cbn [delivered_writes length].
tauto.
- destruct eff as [ret ws zs us cs copyins]. split.
+ intro H.
destruct ws as [|[a bs'] [|? ?]]; try discriminate.
destruct zs as [|? ?]; [|discriminate].
destruct us as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr)
&& bv_eqb ret (len_word (b :: bsr)))
eqn:Hb; try rewrite Hb in H; [|discriminate].
apply andb_true_iff in Hb as [Hb Hr].
apply andb_true_iff in Hb as [Ha Hbs].
apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
inversion H; subst. cbn [delivered_writes].
repeat split; congruence.
+ intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
inversion Heff; subst.
rewrite bv_eqb_refl.
rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
apply (tfo_sys_det segs ms model x8
(mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [])
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFile p (off + len_word bs))) model) U);
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. apply Hchk. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs.
unfold check_read in Hs.
rewrite Hfd32, Hfd in Hs. cbv beta iota in Hs.
rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
rewrite Hfs in Hs. cbv beta iota zeta in Hs.
rewrite in_wmem_si in Hs.
rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs.
cbv beta iota in Hs.
revert Hs.
destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs.
+ exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
+ discriminate.
Qed.
Lemma tfo_write_file : forall ms model x8 p off data bs U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
(bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
fs_lookup (m_fs model) p = Some data ->
negb (modeled_file_gap data off bs) = false ->
w_is0 (ms_gpr ms 2) = false ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms
(with_copyins [(ms_gpr ms 1, length bs)]
(mkEffect (ms_gpr ms 2) [] []))))
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hnz Hh Hlazy Hcont.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
{ rewrite in_mem_si. exact Hrd. }
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins [(ms_gpr ms 1, length bs)] eff (ms_gpr ms 2)
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
{ intro eff.
rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hret : len_word bs = ms_gpr ms 2).
{ unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
{ destruct (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) eqn:Hg'; [|reflexivity].
exfalso. apply andb_prop in Hg' as [Hnz' Hz].
apply Nat.eqb_eq in Hz. apply negb_true_iff in Hnz'.
rewrite Hz in Hlen. cbn in Hlen.
assert (Hzero : ms_gpr ms 2 = Z_to_bv 64 0).
{ rewrite <- (Z_to_bv_bv_unsigned 64 (ms_gpr ms 2)). rewrite <- Hlen. reflexivity. }
unfold w_is0 in Hnz'. rewrite Hzero, bv_eqb_refl in Hnz'. discriminate. }
rewrite Hgate. cbv beta iota.
rewrite Hfs. cbv beta iota.
rewrite Hgap. cbv beta iota.
rewrite Hret.
rewrite Hnz. reflexivity. }
apply (tfo_sys_det segs ms model x8
(with_copyins [(ms_gpr ms 1, length bs)]
(mkEffect (ms_gpr ms 2) [] []))
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.
Lemma tfo_write_file_zero : forall ms model x8 p off data bs U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
(bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
fs_lookup (m_fs model) p = Some data ->
negb (modeled_file_gap data off bs) = false ->
w_is0 (ms_gpr ms 2) = true ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms (mkEffect (ms_gpr ms 2) [] [])))
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hz Hok Hh Hlazy Hcont.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
{ rewrite in_mem_si. exact Hrd. }
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only eff (ms_gpr ms 2)
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
{ intro eff.
rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
rewrite Hfd32, Hfd. cbv beta iota.
rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hret : len_word bs = ms_gpr ms 2).
{ unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
{ rewrite Hz. reflexivity. }
rewrite Hgate. cbv beta iota.
rewrite Hfs. cbv beta iota.
rewrite Hgap. cbv beta iota.
rewrite Hret.
rewrite Hz. cbv beta iota.
unfold check_access_ok_zero. rewrite Hok. reflexivity. }
apply (tfo_sys_det segs ms model x8
(mkEffect (ms_gpr ms 2) [] [])
(with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
(FdFileW p (off + ms_gpr ms 2)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.
Lemma tfo_close : forall ms model x8 e U,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 57%Z ->
fd_lookup (m_fds model) (ms_gpr ms 0) = Some e ->
fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [])))
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model)
U ->
to_fout segs ms model U.
Proof.
intros ms model x8 e U Hsvc Hno Hfd Hfd32 Hh Hlazy Hcont.
assert (Hchk : forall eff,
check_syscall (sys_input segs ms x8) eff model
= check_ret_only eff (Z_to_bv 64 0)
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) []).
{ intro eff.
rewrite (check_syscall_57 segs ms x8 eff model Hno). unfold check_close.
rewrite Hfd32, Hfd. reflexivity. }
apply (tfo_sys_det segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model));
[exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.
Lemma record_gpr : forall regs fr pc sv rv fc mem rom k,
ms_gpr {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} k
= reg_get regs (Z_to_bv 5 (10 + Z.of_nat k)).
Proof. reflexivity. Qed.
Lemma tfo_exit_rec : forall regs pc mem rom model code fsv,
bv_unsigned (getr regs 17) = 93%Z ->
reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
m_fs model = fsv ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
model (fun o => o = (code, fsv)).
Proof.
intros regs pc mem rom model code fsv H17 H10 Hc Hfs.
subst fsv.
eapply (tfo_exit segs _ model (getr regs 17)).
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
- intro o. rewrite record_gpr, arg_reg_0.
rewrite H10, (land_255_small code Hc). tauto.
Qed.
Lemma tfo_read_rec : forall regs pc mem rom model fdv p off data buf cnt U,
bv_unsigned (getr regs 17) = 63%Z ->
reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
fd_lookup (m_fds model) fdv = Some (FdFile p off) ->
fd32 fdv = fdv ->
fs_lookup (m_fs model) p = Some data ->
wseg_ok segs buf (word_to_nat cnt) = true ->
(bv_unsigned cnt <= rw_bytes_max)%Z ->
(0 < bv_unsigned cnt)%Z ->
access_okb buf (bv_unsigned cnt) = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs
(mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
(write_to_mem mem buf (file_read data off cnt)) rom)
(with_fds (fd_insert (m_fds model) fdv
(FdFile p (off + len_word (file_read data off cnt)))) model)
U ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
intros regs pc mem rom model fdv p off data buf cnt U
H17 H10 H11 H12 Hfd Hfd32 Hfs Hwseg Hcnt Hpos Haok Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
assert (Hg1 : ms_gpr ms 1 = buf)
by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
assert (Hg2 : ms_gpr ms 2 = cnt)
by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
apply (tfo_read_file ms model (getr regs 17) p off data w U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- rewrite Hg0. exact Hfd.
- rewrite Hg0. exact Hfd32.
- exact Hfs.
- rewrite Hg1, Hg2. exact Hw.
- rewrite Hg2. exact Hcnt.
- rewrite Hg2. exact Hpos.
- rewrite Hg1, Hg2. exact Haok.
- exact Hh.
- exact Hlazy.
- rewrite Hg0, Hg1, Hg2. unfold ms.
rewrite adv_apply_delivered. exact Hcont.
Qed.
Lemma tfo_write_rec : forall regs pc mem model fdv p off data bs buf cnt U,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
fd_lookup (m_fds model) fdv = Some (FdFileW p off) ->
fd32 fdv = fdv ->
rdn segs mem buf (word_to_nat cnt) = Some bs ->
(bv_unsigned cnt <= rw_bytes_max)%Z ->
fs_lookup (m_fs model) p = Some data ->
negb (modeled_file_gap data off bs) = false ->
(access_okb buf (bv_unsigned cnt) = true \/ (0 < bv_unsigned cnt)%Z) ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs))
(with_fds (fd_insert (m_fds model) fdv (FdFileW p (off + cnt)))
(with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model fdv p off data bs buf cnt U
H17 H10 H11 H12 Hfd Hfd32 Hrd Hcnt Hfs Hgap Hok Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
assert (Hg1 : ms_gpr ms 1 = buf)
by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
assert (Hg2 : ms_gpr ms 2 = cnt)
by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
destruct (w_is0 cnt) eqn:Hz.
-
apply (tfo_write_file_zero ms model (getr regs 17) p off data bs U).
+ unfold ms. cbn [ms_svc_pending]. reflexivity.
+ exact H17.
+ rewrite Hg0. exact Hfd.
+ rewrite Hg0. exact Hfd32.
+ rewrite Hg1, Hg2.
rewrite read_bytes_map_read_byte.
rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
exact Hrd.
+ rewrite Hg2. exact Hcnt.
+ exact Hfs.
+ exact Hgap.
+ rewrite Hg2. exact Hz.
+ destruct Hok as [Hfl | Hp].
* rewrite Hg1, Hg2. exact Hfl.
*
rewrite (w_is0_pos cnt Hp) in Hz. discriminate.
+ exact Hh.
+ exact Hlazy.
+ rewrite Hg0, Hg2. unfold ms.
rewrite adv_eff_ret. exact Hcont.
-
apply (tfo_write_file ms model (getr regs 17) p off data bs U).
+ unfold ms. cbn [ms_svc_pending]. reflexivity.
+ exact H17.
+ rewrite Hg0. exact Hfd.
+ rewrite Hg0. exact Hfd32.
+ rewrite Hg1, Hg2.
rewrite read_bytes_map_read_byte.
rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
exact Hrd.
+ rewrite Hg2. exact Hcnt.
+ exact Hfs.
+ exact Hgap.
+ rewrite Hg2. exact Hz.
+ exact Hh.
+ exact Hlazy.
+ rewrite Hg0, Hg2. unfold ms.
rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
Lemma tfo_close_rec : forall regs pc mem rom model fdv e U,
bv_unsigned (getr regs 17) = 57%Z ->
reg_get regs 10 = fdv ->
fd_lookup (m_fds model) fdv = Some e ->
fd32 fdv = fdv ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fds (fd_remove (m_fds model) fdv) model) U ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} model U.
Proof.
intros regs pc mem rom model fdv e U H17 H10 Hfd Hfd32 Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}).
assert (Hg0 : ms_gpr ms 0 = fdv)
by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
apply (tfo_close ms model (getr regs 17) e U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- rewrite Hg0. exact Hfd.
- rewrite Hg0. exact Hfd32.
- exact Hh.
- exact Hlazy.
- rewrite Hg0. unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.
Lemma tfo_open_enoent_rec : forall regs pc mem model p U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = None ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
mem (seg_rom segs))
model U ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p U H17 H10 H12 Hpath Hdot Hfs Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_openat_enoent ms model (getr regs 17) p U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
- exact Hdot.
- exact Hfs.
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
Lemma tfo_open_rd_rec : forall regs pc mem model p d
(Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
path_eqb p [] = false ->
openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall e, In e openat_errnos ->
to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
mem (seg_rom segs))
model (Te e)) ->
(forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd
(FdFile p (Z_to_bv 64 0))) model) (Ts fd)) ->
(forall o, U o <->
((exists e, In e openat_errnos /\ Te e o)
\/ (exists fd, fd_lookup (m_fds model) fd = None
/\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p d Te Ts U
H17 H10 H12 Hpath Hpe Hdot Hfs Hh Hlazy Herr Hok HU.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_open_core ms model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFile p (Z_to_bv 64 0))) model)
(getr regs 17) (open_copyins ms) Te Ts U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact Hh.
- exact Hlazy.
- intro eff. apply (openat_rd_check segs ms (getr regs 17) model p d).
+ exact H17.
+ unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
+ unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
+ exact Hpe.
+ unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
+ exact Hdot.
+ exact Hfs.
- intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
- intros e HIn.
unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
- intros fd Hlk Hlt.
unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
- exact HU.
Qed.
Lemma tfo_open_wr_rec : forall regs pc mem model p
(Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
path_eqb p [] = false ->
openat_plain_name p = true ->
fs_under (m_fs model) p = false ->
m_halted model = None ->
m_vm_lazy model = [] ->
(forall e, In e openat_errnos ->
to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
mem (seg_rom segs))
model (Te e)) ->
(forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model)) (Ts fd)) ->
(forall o, U o <->
((exists e, In e openat_errnos /\ Te e o)
\/ (exists fd, fd_lookup (m_fds model) fd = None
/\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p Te Ts U
H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Herr Hok HU.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_open_core ms model
(fun fd => with_fds (fd_insert (m_fds model) fd
(FdFileW p (Z_to_bv 64 0)))
(with_fs (fs_set (m_fs model) p []) model))
(getr regs 17) (open_copyins ms) Te Ts U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact Hh.
- exact Hlazy.
- intro eff. apply (openat_wr_check segs ms (getr regs 17) model p).
+ exact H17.
+ unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
+ unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
+ exact Hpe.
+ unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
+ exact Hdot.
+ exact Hun.
- intro fd. split.
+ rewrite with_fds_halted, with_fs_halted. exact Hh.
+ exact Hlazy.
- intros e HIn.
unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
- intros fd Hlk Hlt.
unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
- exact HU.
Qed.
Lemma tfo_open_wr_isdir_rec : forall regs pc mem model p U,
bv_unsigned (getr regs 17) = 56%Z ->
reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
path_eqb p [] = false ->
openat_plain_name p = true ->
fs_under (m_fs model) p = true ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4)
mem (seg_rom segs))
model U ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model p U H17 H10 H12 Hpath Hpe Hdot Hun Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
assert (Hchk : forall eff,
check_syscall (sys_input segs ms (getr regs 17)) eff model
= check_ret_only_copyins (open_copyins ms) eff
(errno_ret EISDIR) model []).
{ intro eff. apply (openat_wr_isdir_check segs ms (getr regs 17) model p).
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- exact Hpe.
- unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
vm_compute. reflexivity.
- exact Hdot.
- exact Hun. }
apply (tfo_sys_det segs ms model (getr regs 17)
(with_copyins (open_copyins ms)
(mkEffect (errno_ret EISDIR) [] [])) model U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- apply check_syscall_ok_iff. rewrite Hchk.
apply check_ret_only_copyins_ok_iff. auto.
- intros eff2 m2 evs2 Hs.
apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
- intro Hs.
apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
rewrite Hchk in Hs.
exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
Lemma tfo_open_toolong_rec : forall regs pc mem model U,
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (reg_get regs 12) = true ->
read_cstr (mrb segs mem) (reg_get regs 11) = CstrTooLong ->
m_halted model = None ->
m_vm_lazy model = [] ->
to_fout segs (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4)
mem (seg_rom segs))
model U ->
to_fout segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}
model U.
Proof.
intros regs pc mem model U H17 Hfl Hpath Hh Hlazy Hcont.
set (ms := {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := seg_rom segs |}).
apply (tfo_openat_toolong ms model (getr regs 17) U).
- unfold ms. cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
- unfold ms. rewrite record_gpr, arg_reg_1.
rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
- exact Hh.
- exact Hlazy.
- unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.
End i.
Lemma fout_omni_run : forall segs pc ph sp brk0 mb rnd lim inp U,
to_fout segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (fout_post U).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto.
cbn [omni_run]. unfold init_config.
exact (to_fout_exec segs _ _ U Hto eq_refl eq_refl).
Qed.
Lemma fout_obs_iff : forall segs pc ph sp brk0 mb rnd lim inp U,
to_fout segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> exists o, U o /\ is_prefix tr (fout_trace o).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
unfold init_config.
set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
by reflexivity.
assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [])
by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (to_fout_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
as (o & Ho & Hp').
exists o. split; [exact Ho | eapply is_prefix_trans; eauto].
- intros (o & Ho & Hp).
destruct (to_fout_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
exists (fout_trace o), c. split; assumption.
Qed.
Lemma fout_no_error_run : forall segs pc ph sp brk0 mb rnd lim inp U,
to_fout segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp) U ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
eapply exec_conseq; [exact (fout_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma fout_omni_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
to_fout source_segs
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U ->
to_fout target_segs
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
Hsource Htarget.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (fout_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
intros tr o (out & _ & _ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.
Lemma fout_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp,
to_fout source_segs
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U ->
to_fout target_segs
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved target_segs) abrk amb asp alim inp) U ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp
Hsource Htarget.
split.
{ apply no_error_run_modeled.
apply (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
right. split.
- intro tr. cbn.
rewrite (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
rewrite (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
reflexivity.
- cbn. apply (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.
Lemma spec_err_escape_equiv :
forall segs pc ph sp brk0 mb rnd lim inp (target : behavior),
all_traces_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target Hall.
left. exact Hall.
Qed.
End g.
