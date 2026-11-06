(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK16 YK0o YK11 YK0j YK0i YK0n YK14 YK1c YK1d.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section g.
Context {fx : FPState}.
Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.

Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
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

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.



Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
apply path_eqb_eq in E. congruence.
Qed.




Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
intros fds k e fd Hne. cbn.
rewrite (bv_eqb_neq k fd Hne). reflexivity.
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




Lemma length_file_read : forall data off count,
length (file_read data off count)
= Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
intros data off count. rewrite file_read_unguarded.
rewrite length_firstn, length_skipn. reflexivity.
Qed.


Lemma firstn_add {A} : forall (l : list A) n m,
firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
induction l as [|x l IH]; intros n m.
- rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
- destruct n as [|n]; [reflexivity|].
cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.

Definition mrb (segs : list Segment) (mem : word -> option byte)
: word -> option byte :=
fun a => match mem a with Some b => Some b | None => seg_rom segs a end.


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




Definition fout_post (U : (word * Fs.Fs) -> Prop) : post :=
fun tr o => exists out, U out /\ tr = fout_trace out /\ exits_with (fst out) tr o.




Definition fon_path (c : config) : Prop :=
(m_halted (cfg_model c) = None
/\ m_vm_lazy (cfg_model c) = []
/\ exists U, to_fout (cfg_ms c) (cfg_model c) U)
\/ m_halted (cfg_model c) <> None.












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





Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

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


















End i.






End g.
