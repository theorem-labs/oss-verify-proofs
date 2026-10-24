(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK1d YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable.Z Require Import Placement.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable.R Require Import Place Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section d.
Context {fx : FPState}.
Lemma v_srli_div : forall (x : word) (sh : Z), (0 <= sh < 64)%Z ->
bv_unsigned (v_srli x sh) = (bv_unsigned x / 2 ^ sh)%Z.
Proof.
intros x sh Hsh. unfold v_srli.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (u64_range x) as Hx.
assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
by (apply Z.div_le_upper_bound; nia).
assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
apply Z.mod_small. lia.
Qed.
Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
[Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
rewrite <- N_to_le_bytes_1_small.
apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.
Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
(a v : word) (b : byte),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
getr regs rs2 = v ->
Z_to_bv 8 (bv_unsigned v) = b ->
RiscvSemantics.store_ok segs mem a 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv, Hb. reflexivity.
- rewrite Ha. exact Hok.
Qed.
Lemma wbytes_snoc : forall (bs : list byte) (m : word -> option byte)
(a : word) (b : byte),
wbytes m a (bs ++ [b]) = wbytes (wbytes m a bs) (a + nat_to_word (length bs)) [b].
Proof.
induction bs as [|x bs IH]; intros m a b.
- cbn [app wbytes length]. rewrite word_add_0. reflexivity.
- cbn [app wbytes length].
rewrite IH. f_equal.
rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
zmem m a n.
Lemma zfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
zfill a n m x = m x.
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.
Lemma rdn_zfill_out : forall segs a n m (x : word) k,
(bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
(bv_unsigned x + Z.of_nat k <= bv_unsigned a
\/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
rdn segs (zfill a n m) x k = rdn segs m x k.
Proof.
intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.
Definition munmap_model (addr n : word) (m : Model) : Model :=
with_mmap_destroyed addr n
(mkVmMapsFull (vm_reserved (m_vmmaps m))
(map_remove (vm_maps (m_vmmaps m)) addr)
(maps_subtract (vm_noaccess (m_vmmaps m))
(bv_unsigned addr)
(bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.
Definition mmap_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
(vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.
Definition page_round_up (len : word) : word :=
Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
&& (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.
Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma munmap_model_fs : forall addr n m, m_fs (munmap_model addr n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma munmap_model_fd1chan : forall addr n m, fd1chan m -> fd1chan (munmap_model addr n m).
Proof. intros addr n m H. exact H. Qed.
Lemma munmap_model_no_lazy : forall addr n m,
m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
vm_forget_range, with_vm_backing, with_vmmaps.
cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma mmap_model_halted : forall a n m, m_halted (mmap_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_fs : forall a n m, m_fs (mmap_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_fd1chan : forall a n m, fd1chan m -> fd1chan (mmap_model a n m).
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_lazy : forall a n m,
m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma grant_ok_unpack : forall hint m a n,
grant_ok hint m a n = true ->
(bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
(bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\
(vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z.
Proof.
intros hint m a n H. unfold grant_ok in H.
rewrite !andb_true_iff in H.
destruct H as [[[[H1 H2] H3] H4] H5].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
apply Z.leb_le in H5.
auto 7.
Qed.
Lemma region_free_cons : forall (b s : word) r (lo n : word),
region_free ((b, s) :: r) lo n = true ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b
\/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
/\ region_free r lo n = true.
Proof.
intros b s r lo n H. cbn [region_free] in H.
apply andb_true_iff in H. destruct H as [H1 H2].
split; [|exact H2].
apply negb_true_iff in H1. unfold iv_overlap in H1.
apply andb_false_iff in H1.
destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.
Lemma source_alloc_limit_val : source_alloc_limit = 0x400000000%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma target_alloc_limit_val : target_alloc_limit = 0x8000000000%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma in_arg3_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.
Lemma in_arg4_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.
Lemma in_arg5_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.
Definition mmap_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.
Lemma mmap_args_ok_gates : forall ms,
mmap_args_ok ms ->
mmap_off_aligned_b (ms_gpr ms 5) = true /\
mmap_anon_b (ms_gpr ms 3) = true /\
w_is0 (ms_gpr ms 1) = false /\
mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
= true.
Proof.
intros ms (H1 & H2 & H3 & H4 & H5).
split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
(bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
ms_gpr ms 1 <> Z_to_bv 64 0 /\
(bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) = true.
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].
Lemma syscall_spec_munmap : forall segs ms x8 model o,
bv_unsigned x8 = 215%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.
Lemma munmap_check_modeled : forall ms model eff,
munmap_args_ok ms model ->
check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if w_is0 r
&& listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms model eff (Hal & Hlen & Hnw & Hhas).
unfold check_munmap.
rewrite (proj2 (Z.eqb_eq _ _) Hal).
unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
cbn [negb orb]. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.
Lemma munmap_ok : forall segs ms x8 model,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
syscall_spec (sys_input segs ms x8) model
(Ok (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros segs ms x8 model Hno Ha.
apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
rewrite (munmap_check_modeled ms model _ Ha).
unfold munmap_eff, w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.
Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
eff = munmap_eff ms /\
model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model
/\ evs = [].
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply check_munmap_complete_ok in Hspec.
rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
[destruct zs as [|? ?]|]; try discriminate.
destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
destruct (w_is0 r
&& listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
eqn:HC; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in HC as [Hr Hus].
unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
apply listNN_eqb_eq in Hus; subst us.
unfold munmap_eff. auto.
Qed.
Lemma munmap_no_unmodeled : forall segs ms x8 model,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
destruct (w_is0 (Z_to_bv 64 0)
&& listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
discriminate.
Qed.
Lemma syscall_spec_mmap : forall segs ms x8 model o,
bv_unsigned x8 = 222%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
(ms_gpr ms 4) (ms_gpr ms 5) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.
Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.
Lemma mmap_errno_range : forall e,
In e mmap_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.
Lemma grant_not_errno : forall hint model a n,
(0 <= n)%Z -> grant_ok hint model a n = true ->
errno_ret_in mmap_errnos a = false.
Proof.
intros hint model a n Hn Hg.
destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
apply errno_ret_in_below; [reflexivity|].
alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
Lemma grant_ok_not_refusable : forall hint model a n,
grant_ok hint model a n = true ->
mmap_grant_refusable (Z_to_bv 64 34) model n = false.
Proof.
intros hint model a n Hg. unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[[H1 H2] H3] H4] H5].
unfold mmap_grant_refusable.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false) by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok. rewrite Hnr, H5.
rewrite (vm_find_base_complete (m_vmmaps model) n a) by (unfold vm_base_ok; rewrite H1, H2, H3, H4; reflexivity).
reflexivity.
Qed.
Lemma mmap_succ_ok : forall segs ms x8 model a,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
(mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros segs ms x8 model a Hno Ha Hg.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite (grant_not_errno (ms_gpr ms 0) model a
(page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
| exact Hg ].
unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[[H1 H2] H3] H4] H5].
rewrite Hflags.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
rewrite H1, H2, H3, H4, H5.
unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
reflexivity.
Qed.
Lemma mmap_ok_inv : forall segs ms x8 model eff model' evs,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\
((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
/\ model' = model) \/
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
/\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
/\ model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)).
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply check_mmap_complete_ok in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
rewrite Hflags in Hspec.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
rewrite Hnr in Hspec.
destruct eff as [r ws zs us cs copyins].
cbv beta iota zeta in Hspec.
destruct ws as [|w ws]; [|discriminate].
destruct us as [|u us]; [|discriminate].
destruct cs as [|c cs]; [|discriminate].
destruct copyins as [|copyin copyins]; [|discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Herr;
rewrite ?Herr in Hspec; cbv beta iota in Hspec.
- destruct zs as [|z zs]; [|discriminate].
apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
inversion Hspec; subst.
split; [reflexivity|]. left.
exists e. auto.
- destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
&& (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
&& region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
&& (vm_backing_used model
+ page_round_up_Z (bv_unsigned (ms_gpr ms 1))
<=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
rewrite ?Hcond in Hspec.
2:{ rewrite andb_false_l in Hspec. discriminate. }
destruct (listNN_eqb zs
[(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
rewrite ?Hzs in Hspec.
2:{ rewrite andb_false_r in Hspec. discriminate. }
cbn [andb] in Hspec.
apply listNN_eqb_eq in Hzs. subst zs.
inversion Hspec; subst.
split; [reflexivity|]. right.
exists r. split; [|split].
+ unfold grant_ok. exact Hcond.
+ unfold page_round_up. reflexivity.
+ reflexivity.
Qed.
Lemma grant_of_not_refusable : forall hint model nZ,
mmap_grant_refusable (Z_to_bv 64 34) model nZ = false ->
exists a, grant_ok hint model a nZ = true.
Proof.
intros hint model nZ H. unfold mmap_grant_refusable in H.
apply orb_false_iff in H as [Hb Hg]. apply negb_false_iff in Hb. apply negb_false_iff in Hg.
destruct (vm_gap_available_find _ _ Hg) as [a Ha].
destruct (vm_find_base_sound _ _ _ Ha) as (H1 & H2 & H3 & H4).
exists a. unfold grant_ok.
rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4.
unfold mmap_noreserve_backed_ok in Hb.
change (mmap_noreserve_b (Z_to_bv 64 34)) with false in Hb. cbv iota in Hb. rewrite Hb. reflexivity.
Qed.
Lemma mmap_refusal_refusable : forall segs ms x8 model e,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
In e mmap_errnos ->
~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (mkEffect (errno_ret e) [] []) ->
mmap_grant_refusable (Z_to_bv 64 34) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true.
Proof.
intros segs ms x8 model e Hno Ha HIn Hns.
destruct (mmap_grant_refusable (Z_to_bv 64 34) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hrf;
[reflexivity | exfalso].
destruct (grant_of_not_refusable (ms_gpr ms 0) model _ Hrf) as [a Hg].
apply Hns.
apply (refusal_spurious_of_grant ACFG _ model _ (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
(mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
- apply acfg_family_off_222. exact Hno.
- cbn [eff_ret]. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno).
apply ret_in_errnos_errno. exact HIn.
- apply mmap_succ_ok; assumption.
- cbn [eff_ret]. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno).
change (ret_in_errnos mmap_errnos a) with (errno_ret_in mmap_errnos a).
apply (grant_not_errno (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia | exact Hg].
Qed.
Lemma mmap_grant_nonspurious : forall segs ms x8 model a,
bv_unsigned x8 = 222%Z ->
grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]).
Proof.
intros segs ms x8 model a Hno Hg. apply spurious_refusal_not_refusal. cbn [eff_ret].
rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno).
change (ret_in_errnos mmap_errnos a) with (errno_ret_in mmap_errnos a).
apply (grant_not_errno (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia | exact Hg].
Qed.
Lemma mmap_refusable_forced : forall segs ms x8 model eff,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
mmap_grant_refusable (Z_to_bv 64 34) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff.
Proof.
intros segs ms x8 model eff Hno Ha Hrf. apply not_spurious_forced. intros eff' m' evs' Hs.
destruct (mmap_ok_inv segs ms x8 model eff' m' evs' Hno Ha Hs) as (_ & [(e & He & -> & _) | (a & Hg & _ & _)]).
- cbn [eff_ret]. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno).
apply ret_in_errnos_errno. exact He.
- exfalso. rewrite (grant_ok_not_refusable _ _ _ _ Hg) in Hrf. discriminate Hrf.
Qed.
Lemma mmap_no_unmodeled : forall segs ms x8 model,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno Ha Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
cbv beta iota zeta in Hspec.
match type of Hspec with context [errno_ret_in ?es (Z_to_bv 64 0)] =>
rewrite (errno_ret_in_below es (Z_to_bv 64 0)) in Hspec;
[| reflexivity | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; unfold two_pow_64; lia]
end.
cbv beta iota in Hspec.
match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
discriminate.
Qed.
Lemma adv_mmap_grant : forall regs pc sv mem rom a n,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
(mkEffect a [] [(a, n)]))
= mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
Proof.
intros regs pc sv mem rom a n.
assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
{ cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies
apply_writes apply_copies].
unfold mkst, regupd.
rewrite b_npc4, Hm. reflexivity.
Qed.
Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
&& Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
then None else m x.
Lemma unfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
unfill a n m x = m x.
Proof.
intros a n m x Hx. unfold unfill.
destruct Hx as [Hx | Hx].
- rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
rewrite andb_false_r. reflexivity.
Qed.
Lemma rdn_unfill_out : forall segs a n m (x : word) k,
(bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
(bv_unsigned x + Z.of_nat k <= bv_unsigned a
\/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
rdn segs (unfill a n m) x k = rdn segs m x k.
Proof.
intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
intros y Hy. apply unfill_out. lia.
Qed.
Lemma adv_munmap : forall regs pc sv mem rom a n,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv;
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
(mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []))
= mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom.
Proof.
intros regs pc sv mem rom a n.
assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
= unfill a n mem).
{ cbn [apply_writes apply_zeros].
apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity. }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
unfold mkst, regupd.
rewrite b_npc4, Hm. reflexivity.
Qed.
Section f.
Variable segs : list Segment.
Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
(1 <= length buf)%nat ->
twm_pend ms model buf bufs code ->
twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm ms' model bufs code ->
twm ms model bufs code
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
(skipn n rest) bufs code) ->
twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
twm ms model bufs code ->
twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
(1 <= length rest)%nat ->
twm_pend ms model rest bufs code ->
twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.
Scheme twm_min := Minimality for twm Sort Prop
with twm_pend_min := Minimality for twm_pend Sort Prop
with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.
Lemma msteps_twm : forall ms ms' model bufs code,
msteps segs ms ms' -> twm ms' model bufs code -> twm ms model bufs code.
Proof.
intros ms ms' model bufs code H; induction H; [auto|].
intro Hw. eapply twm_step; eauto.
Qed.
Lemma msteps_twm_tail : forall ms ms' model rest bufs code,
msteps segs ms ms' -> twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.
Proof.
intros ms ms' model rest bufs code H; induction H; [auto|].
intro Hw. eapply twmt_step; eauto.
Qed.
Lemma twm_write_ret : forall regs pc mem rom model buf bufs code,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = Z_to_bv 64 1 ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
twm_tail (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
model (skipn n buf) bufs code) ->
twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
model (buf :: bufs) code.
Proof.
intros regs pc mem rom model buf bufs code H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
apply twm_write; [exact Hnb|].
eapply twmp_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.
Lemma twm_tail_write_rec : forall regs pc mem rom model rest bufs code,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = Z_to_bv 64 1 ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
twm_tail (mkst (regupd regs 10 (len_word (firstn n rest))) (v_addi pc 4) mem rom)
model (skipn n rest) bufs code) ->
twm_tail {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
model rest bufs code.
Proof.
intros regs pc mem rom model rest bufs code H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
apply twmt_more; [exact Hnb|].
eapply twmp_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.
Lemma twm_munmap_rec : forall regs pc mem rom model bufs code (a nlen : word),
bv_unsigned (getr regs 17) = 215%Z ->
reg_get regs 10 = a ->
reg_get regs 11 = nlen ->
(bv_unsigned a mod page_size = 0)%Z ->
nlen <> Z_to_bv 64 0 ->
(bv_unsigned a + page_round_up_Z (bv_unsigned nlen) <= TASK_SIZE)%Z ->
map_has (vm_maps (m_vmmaps model)) a (page_round_up nlen) = true ->
twm (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(unfill a (page_round_up nlen) mem) rom)
(munmap_model a (page_round_up nlen) model) bufs code ->
twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
model bufs code.
Proof.
intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
eapply twm_munmap.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
rewrite E10, E11, Ha, Hn. auto.
- unfold munmap_eff, ms_gpr. cbn [ms_regs].
rewrite E10, E11, Ha, Hn.
rewrite adv_munmap. exact Hcont.
Qed.
Lemma twm_exit_coden : forall regs pc mem rom model (c : word),
bv_unsigned (getr regs 17) = 93%Z ->
reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
twm {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
model [] c.
Proof.
intros regs pc mem rom model c H17 H10 Hc.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |} 0)
(Z_to_bv 64 255) = c).
{ unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
apply land_255_small. exact Hc. }
rewrite <- Hg.
eapply twm_exit.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
Qed.
Lemma sstep_munmap_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
subst eff model' evs0
end.
match goal with
| Hmat : materialize_model_accesses
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
inversion Hmat; subst
end.
split; reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (Heff & Hm & Hevs); subst eff model' evs0;
rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hm & _);
subst model';
assert (Hhn : m_halted
(munmap_model (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite munmap_model_halted; exact Hh);
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.
Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.
Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
(fs : Fs.Fs) : post :=
fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
/\ exits_with code tr o.
Lemma twm_exec_mut :
(forall ms model bufs code, twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
/\ (forall ms model rest bufs code, twm_pend ms model rest bufs code ->
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
/\ (forall ms model rest bufs code, twm_tail ms model rest bufs code ->
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))).
Proof.
apply (twm_mutind
(fun ms model bufs code =>
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
(fun ms model rest bufs code =>
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
(fun ms model rest bufs code =>
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))).
-
intros ms model x8 Hsvc Hx8 Hbm Hh Hlazy Hfd.
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
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold twm_post. cbn beta. rewrite app_nil_r. cbn [wevents app]. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
intros ms model buf bufs code Hnb Hp IH Hbm Hh Hlazy Hfd.
apply Forall_cons_iff in Hbm as [Hb Hbs].
eapply exec_conseq; [exact (IH Hb Hbs Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx].
rewrite Heq. cbn [wevents]. rewrite <- app_assoc. reflexivity.
-
intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hbm Hh Hlazy Hfd.
assert (Hh' : m_halted
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite munmap_model_halted; exact Hh).
assert (Hfd' : fd1chan
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
by (apply munmap_model_fd1chan; exact Hfd).
apply (exec_step_only segs _ _ []
(mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
+ apply (sstep_syscall segs ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
* exact Hh.
* exact Hsvc.
* apply munmap_ok; [exact Hno | exact Hargs].
* exact Hh'.
* apply materialize_model_accesses_no_lazy.
exact (munmap_model_no_lazy _ _ _ Hlazy).
+ intros evs st Hss.
exact (sstep_munmap_inv ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss).
+ eapply exec_conseq;
[exact (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') |].
intros tr o (Heq & Hx). split; [| exact Hx].
cbn [app]. rewrite Heq, munmap_model_fs. reflexivity.
-
intros ms ms' model bufs code Hsvc Hstep Hte IH Hbm Hh Hlazy Hfd.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
-
intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hbr Hbm Hh Hlazy Hfd.
apply exec_step; [exact Hh | | |].
+ eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv (Z_to_bv 64 1)) (firstn (length rest) rest))).
* exact Hh.
* exact Hsvc.
* apply write1_ok_n; try assumption. apply Nat.le_refl.
* exact Hh.
* apply materialize_model_accesses_no_lazy. exact Hlazy.
+ intros evs Hss.
destruct (sstep_write_inv segs ms model x8 rest evs SError
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & _ & _ & _ & Habs).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_write_inv segs ms model x8 rest evs (SNext c')
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
injection Hc' as ->.
eapply exec_conseq;
[exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx].
rewrite Heq. rewrite <- (firstn_skipn n rest) at 3.
rewrite map_app, <- !app_assoc. reflexivity.
-
intros ms model bufs code Hte IH Hbr Hbm Hh Hlazy Hfd.
eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx]. cbn [map app]. exact Heq.
-
intros ms model rest bufs code Hnb Hp IH Hbr Hbm Hh Hlazy Hfd.
exact (IH Hbr Hbm Hh Hlazy Hfd).
-
intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hbr Hbm Hh Hlazy Hfd.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbr Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma twm_exec : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)).
Proof. intros ms model bufs code Hte. exact (proj1 twm_exec_mut ms model bufs code Hte). Qed.
Lemma twm_star_admits : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
exists c, star segs (mkCfg ms model) (wevents bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd.
destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.
Lemma twm_star_only : forall ms model bufs code,
twm ms model bufs code ->
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (wevents bufs ++ [ExitEv code (m_fs model)]).
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar))
as (tr' & o & _ & Heq & _).
rewrite <- Heq. apply is_prefix_app.
Qed.
Inductive tmw : machine_state -> Model -> list (list byte) -> word
-> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
(forall e, In e mmap_errnos ->
twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
(forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
tmw ms' model bf cf bs cs ->
tmw ms model bf cf bs cs.
Lemma msteps_tmw : forall ms ms' model bf cf bs cs,
msteps segs ms ms' -> tmw ms' model bf cf bs cs -> tmw ms model bf cf bs cs.
Proof.
intros ms ms' model bf cf bs cs H; induction H; [auto|].
intro Hw. eapply tmw_step; eauto.
Qed.
Lemma tmw_mmap_rec : forall regs pc mem rom model bf cf bs cs,
bv_unsigned (getr regs 17) = 222%Z ->
reg_get regs 11 <> Z_to_bv 64 0 ->
reg_get regs 12 = Z_to_bv 64 3 ->
reg_get regs 13 = Z_to_bv 64 34 ->
reg_get regs 14 = Z_to_bv 64 (-1) ->
reg_get regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
twm (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf) ->
(forall a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true ->
twm (mkst (regupd regs 10 a) (v_addi pc 4)
(zfill a (page_round_up (reg_get regs 11)) mem) rom)
(mmap_model a (page_round_up (reg_get regs 11)) model) bs cs) ->
(exists a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) ->
tmw {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
model bf cf bs cs.
Proof.
intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
Hfail Hsucc Hex.
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
assert (E13 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
assert (E14 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
assert (E15 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
eapply tmw_mmap.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold mmap_args_ok, ms_gpr. cbn [ms_regs].
rewrite E11, E12, E13, E14, E15.
auto.
- intros e HIn. rewrite adv_set. apply Hfail; assumption.
- intros a Hg. rewrite adv_mmap_grant.
unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
apply Hsucc. exact Hg.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.
Lemma sstep_mmap_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
sstep_cfg segs ACFG (mkCfg ms model) evs st ->
evs = [] /\
((exists e, In e mmap_errnos /\
mmap_grant_refusable (Z_to_bv 64 34) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model)))).
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
subst evs0
end.
split; [reflexivity|].
destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
+ match goal with Hns : ~ spurious_refusal_cfg _ _ _ _ |- _ =>
pose proof (mmap_refusal_refusable segs ms x8 model e Hno Hargs HIn Hns) as Hrf end.
left. exists e.
match goal with
| Hmat : materialize_model_accesses model _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
inversion Hmat; subst
end.
split; [assumption |]. split; [exact Hrf |].
rewrite apply_effect_no_write. reflexivity.
+ match goal with
| Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
inversion Hmat; subst
end.
right. exists a. auto.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
| rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite Hh in H6; discriminate
| rewrite mmap_model_halted, Hh in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
[ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
| assert (Hhn : m_halted
(mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite mmap_model_halted; exact Hh);
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.
End f.
End d.
