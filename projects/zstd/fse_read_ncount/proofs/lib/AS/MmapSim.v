(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (adds grant_ok, a grant at Linux's placement (linux_place_is) below alloc_top, on a free range and within the limit, with grant_ok_intro and grant_ok_place; munmap_model via mmap_fixed_destroyed_next; munmap's munmap_errnos answer, which leaves the model alone, in munmap_check_modeled, munmap_ok_inv, sstep_munmap_inv and twm's munmap step, with munmap_fail_ok and ENOMEM_in_munmap_errnos; twm's write step takes an access_okb premise on the buffer; munmap_ok and munmap_no_unmodeled re-proved; adds iv_subtract_outside, maps_subtract_exact and munmap_node_cfg, munmap's step under ACFG; imports Cfg, Placement and ExecutableSpecs). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
(* ACFG is this unit's OWN Lib/Cfg.v:14 (Definition ACFG : SpuriousCfg := alloc_only_cfg
   false), not a model name, and this file never required it -- "The reference ACFG was not
   found in the current environment" at :296 without it (measured). The sibling
   zstd/simple_decompress AS/MmapSim.v carries exactly this line. Lib/Cfg imports only model
   modules, so it cannot close a cycle with AS/. *)
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.
#[using="Type"] Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
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
#[using="Type"] Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
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
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
zmem m a n.
#[using="Type"] Lemma zfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
zfill a n m x = m x.
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.
Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.
Lemma iv_subtract_outside : forall (b s : word) lo hi,
  (0 < bv_unsigned s)%Z -> (lo < hi)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  iv_subtract b s lo hi = [(b, s)].
Proof.
  intros b s lo hi Hs Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b)%Z
      with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_exact : forall l (a n : word),
  (0 < bv_unsigned n)%Z ->
  (forall b s, In (b, s) l -> (0 < bv_unsigned s)%Z) ->
  (forall b s, In (b, s) l -> b = a -> s = n) ->
  (forall b s, In (b, s) l -> b <> a ->
     (bv_unsigned b + bv_unsigned s <= bv_unsigned a
      \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b)%Z) ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  = map_remove l a.
Proof.
  induction l as [|[b s] r IH]; intros a n Hn Hpos Hu Hd; [reflexivity|].
  assert (IHr : maps_subtract r (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
                = map_remove r a).
  { apply IH; [exact Hn
              | intros b' s' H; apply (Hpos b' s'); right; exact H
              | intros b' s' H; apply (Hu b' s'); right; exact H
              | intros b' s' H; apply (Hd b' s'); right; exact H]. }
  cbn [maps_subtract]. rewrite IHr.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove r a).
  destruct (bv_eqb b a) eqn:E; cbn [negb].
  - apply bv_eqb_eq in E. subst b.
    rewrite (Hu a s (or_introl eq_refl) eq_refl).
    unfold iv_subtract. cbv zeta.
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
    reflexivity.
  - assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in E; discriminate).
    rewrite (iv_subtract_outside b s); [reflexivity | | lia |].
    + exact (Hpos b s (or_introl eq_refl)).
    + exact (Hd b s (or_introl eq_refl) Hne).
Qed.

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
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.
Lemma grant_ok_intro : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  grant_ok hint m a n = true.
Proof.
  intros hint m a n Hn Hnal Hpl Hbud.
  destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok. rewrite Hpl, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop), (proj2 (Z.leb_le _ _) Hbud).
  reflexivity.
Qed.

#[using="Type"] Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
#[using="Type"] Lemma munmap_model_no_lazy : forall addr n m,
m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
vm_forget_range, with_vm_backing, with_vmmaps.
cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma grant_ok_place : forall hint m a n,
  grant_ok hint m a n = true ->
  linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

#[using="Type"] Lemma region_free_cons : forall (b s : word) r (lo n : word),
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
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
(bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
ms_gpr ms 1 <> Z_to_bv 64 0 /\
(bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) = true.
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].
#[using="Type"] Lemma syscall_spec_munmap : forall segs ms x8 model o,
bv_unsigned x8 = 215%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.
#[using="Type"] Lemma munmap_check_modeled : forall ms model eff,
munmap_args_ok ms model ->
check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in munmap_errnos r
then match us with
| [] => CheckOk model []
| _ => CheckReject
end
else if w_is0 r
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
#[using="Type"] Lemma munmap_ok : forall segs ms x8 model,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
syscall_spec (sys_input segs ms x8) model
(Ok (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros segs ms x8 model Hno Ha.
apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
rewrite (munmap_check_modeled ms model _ Ha).
unfold munmap_eff, w_is0.
replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by reflexivity.
cbv beta iota. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.
Lemma munmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  In e munmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.

Lemma ENOMEM_in_munmap_errnos : In ENOMEM munmap_errnos.
Proof. left. reflexivity. Qed.

#[using="Type"] Lemma munmap_ok_inv : forall segs ms x8 model eff model' evs,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\
((exists e, In e munmap_errnos /\
eff = mkEffect (errno_ret e) [] [] /\ model' = model)
\/ (eff = munmap_eff ms /\
model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply check_munmap_complete_ok in Hspec.
rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
[destruct zs as [|? ?]|]; try discriminate.
destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
destruct (errno_ret_in munmap_errnos r) eqn:He.
- destruct us as [|? ?]; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
split; [reflexivity|]. left. exists e. auto.
- destruct (w_is0 r
&& listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
eqn:HC; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in HC as [Hr Hus].
unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
apply listNN_eqb_eq in Hus; subst us.
split; [reflexivity|]. right. unfold munmap_eff. auto.
Qed.
#[using="Type"] Lemma munmap_no_unmodeled : forall segs ms x8 model,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false in Hspec
by reflexivity.
cbv beta iota in Hspec.
destruct (w_is0 (Z_to_bv 64 0)
&& listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
discriminate.
Qed.
Lemma munmap_node_cfg : forall segs ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  (forall i : unit, sstep_cfg segs ACFG (mkCfg ms model) ((fun _ => []) i)
       (SNext ((fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                                (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) i)))
  /\ (forall e st, sstep_cfg segs ACFG (mkCfg ms model) e st ->
        exists i : unit, e = (fun _ => []) i
          /\ st = SNext ((fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) i)).
Proof.
  intros segs ms model x8 Hh Hlazy Hsvc Hno Hargs.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215%Z) by exact Hno.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model
                             = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model).
  { intros eff. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. }
  pose proof (fun eff => eq_trans (Hchk eff) (munmap_check_modeled ms model eff Hargs)) as Hck0.
  clear Hchk.
  assert (Hne : errno_ret_in munmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  assert (HR : forall r, refusal_b (sys_input segs ms x8) model r = errno_ret_in munmap_errnos r)
    by (intros r; unfold refusal_b; rewrite Hno'; reflexivity).
  assert (Hoff : injected_family_off ACFG (sys_input segs ms x8) = true)
    by (unfold injected_family_off; rewrite Hno'; reflexivity).
  apply (node_chk_grant_cfg segs ms model x8 unit
           (fun _ => munmap_eff ms)
           (fun _ => munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
           (fun _ => []) tt Hh Hsvc Hoff).
  - intros []. rewrite Hck0. unfold munmap_eff. cbv beta iota. rewrite Hne. unfold w_is0. rewrite bv_eqb_refl.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros []. rewrite HR. exact Hne.
  - intros [r ws zs us cs ci] m' evs Hck Hr. rewrite HR in Hr. cbn [eff_ret] in Hr. rewrite Hck0 in Hck.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    cbv beta iota in Hck. rewrite Hr in Hck. cbv beta iota in Hck.
    destruct (w_is0 r) eqn:E0; [|discriminate].
    destruct (listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]) eqn:Hl; [|discriminate].
    apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck.
    injection Hck as <- <-.
    unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
    exists tt. unfold munmap_eff. repeat split; reflexivity.
  - intros [r ws zs us cs ci] m' evs Hck Hr. rewrite HR in Hr. cbn [eff_ret] in Hr. rewrite Hck0 in Hck.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    cbv beta iota in Hck. rewrite Hr in Hck. cbv beta iota in Hck.
    destruct us; [|discriminate]. injection Hck as <- _. exact Hh.
  - intros [r ws zs us cs ci] Hck. rewrite Hck0 in Hck.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in munmap_errnos r); [destruct us; discriminate|].
    destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
  - intros []. cbv beta. rewrite munmap_model_halted. exact Hh.
  - intros []; reflexivity.
Qed.

Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
&& Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
then None else m x.
#[using="Type"] Lemma unfill_out : forall a n m (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
unfill a n m x = m x.
Proof.
intros a n m x Hx. unfold unfill.
destruct Hx as [Hx | Hx].
- rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
rewrite andb_false_r. reflexivity.
Qed.
Section WithSegs.
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
    (forall e, In e munmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bufs code) ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(* [comment removed for export] *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* [comment removed for export] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
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
#[using="Type"] Lemma sstep_munmap_inv : forall ms model x8 evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\
((exists e, In e munmap_errnos /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (Hevs & Hcase);
subst evs0
end.
split; [reflexivity|].
destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
+ left. exists e.
match goal with
| Hmat : materialize_model_accesses model _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
inversion Hmat; subst
end.
split; [assumption |].
rewrite apply_effect_no_write. reflexivity.
+ right.
match goal with
| Hmat : materialize_model_accesses
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
inversion Hmat; subst
end.
reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
[ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
| rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
[ rewrite Hh in H6
| rewrite munmap_model_halted, Hh in H6 ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
[ rewrite (m_killed_of_m_halted_none _ Hh) in H6
| rewrite m_killed_of_m_halted_none in H6;
[| rewrite munmap_model_halted; exact Hh] ];
discriminate
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
End WithSegs.
End WithFP1.
