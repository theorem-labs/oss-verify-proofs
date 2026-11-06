(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/U/Reusable/YN3e.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/U/Reusable/YN3e_cfw.v, with its module paths and addresses changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP08 YP04 YL02 YN3u.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YH00 YH01 YN3h.
From OSSVerify.libreac.fuzz_decode.images Require Import Ubsan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0d YH02 YN3e YK15_cfw YP03_cfw YP0n2_cfw SymTac_cfw.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.
Section f.
Variable sp : word.
Variable argv envp : list (list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfits : entry_stack_fits sp argv envp.
Variable uid hw : word.
Variable rnd : EntryDraw.
Ltac csym_spliceL HS Hms k E' Hagree upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply crealizes_msteps; [assumption | assumption | exact Hms | ];
rewrite Hshape in HS; clear Hshape;
unshelve epose proof (st_ok_set_regs segs k E E' ss _ regs' _ pc' _ upd HS Hagree _ _ _ _ _);
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
|
|
| clear HS Hms;
match goal with Hn : st_ok _ _ (set_regs_pc _ _ _) _ |- _ => rename Hn into HS end;
sym_norm HS ]
end end.
Ltac reg_of HS r H :=
pose proof (st_ok_reg src0segs _ _ _ r HS) as H;
eval_sr_get_in H; cbn [sv_denot] in H; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H.
Ltac sym_add_chunk_sem HS b c :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (add_chunk_sem (ss_mem ss) b c) in
lazymatch r with
| Some (?rs', ?cs) =>
let H := fresh "Hadd" in let HS' := fresh "HS'" in
assert (H : add_chunk_sem (ss_mem ss) b c = Some (rs', cs)) by (vm_compute; reflexivity);
unshelve epose proof (st_ok_add_chunk_sem segs E ss ms b c rs' cs HS H _) as HS';
[ cbn [base_val ms_mem]
| clear H HS; rename HS' into HS;
lazymatch type of HS with st_ok _ _ ?ss2 _ =>
let ss3 := eval vm_compute in ss2 in change (st_ok segs E ss3 ms) in HS end ]
| None => fail "sym_add_chunk_sem: chunk not inside a region of that base"
end
end.
Lemma src0_start_gen_cf : forall (two : bool) model T,
(if two then (2 <= length argv)%nat else True) ->
m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src0segs (E_main sp argv envp tid rnd) (ss_main two) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp argv envp rnd) ->
crealizes src0_msyms (mkCfg ms (with_tid tid model)) T) ->
crealizes src0_msyms (mkCfg (init_machine_state src0segs Ubsan_init_pc Ubsan_phdrs sp rnd argv envp uid hw) model) T.
Proof using Hsp Hva Hve Hfits.
intros two model T Htwo Hh Hlz Htid K.
pose proof (layout_facts sp argv envp Hsp Hva Hve) as L. unfold SP_LO, SP_HI in L.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
pose proof (src0_init_st_ok sp argv envp uid hw rnd (xw_main sp argv envp (Z_to_bv 64 0) rnd) (xd_st uid hw rnd) two
Hsp Hva Hve Hfits eq_refl eq_refl eq_refl Htwo) as HS.
change (st_ok src0segs (E_st sp argv envp uid hw rnd (Z_to_bv 64 0)) (src0_ss0 two)
(init_machine_state src0segs Ubsan_init_pc Ubsan_phdrs sp rnd argv envp uid hw)) in HS.
apply (st_ok_add_alias src0segs _ _ _ (fst alias_memset) (snd alias_memset)) in HS; [|apply (YN3e.alias_memset_ok sp argv envp Hsp uid hw rnd)].
apply (st_ok_add_alias src0segs _ _ _ (fst alias_envp) (snd alias_envp)) in HS; [|apply (YN3e.alias_envp_ok sp argv envp Hsp Hva Hve uid hw rnd)].
change (st_ok src0segs (E_st sp argv envp uid hw rnd (Z_to_bv 64 0)) (ss_start two)
(init_machine_state src0segs Ubsan_init_pc Ubsan_phdrs sp rnd argv envp uid hw)) in HS.
pose proof (runs_main_init sp argv envp Hsp Hva Hve two Ubsan_init_pc uid hw rnd Htwo) as HR.
destruct two.
all: csym_run_with src0tbl_ok HS.
all: idtac "PHASE B".
all: reg_of HS (9%bv:reg) H9.
all: lazymatch goal with |- crealizes _ (mkCfg ?ms _) _ =>
destruct ((YN3e.envp_block_reads sp argv envp Hsp Hva Hve uid hw rnd) (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 0 _ _ HR eq_refl))
as (Hnz & Hz & Hnw);
destruct (src0_envp_count (length envp) (ms_regs ms) (ms_mem ms) (seg_rom src0segs) _ H9 Hnz Hz Hnw)
as (regs1 & Hms & R10 & R9 & Rfr) end.
all: lazymatch type of HS with st_ok _ ?E _ _ =>
csym_spliceL HS Hms 9%nat E (env_agree_refl 9%nat E) upd_envp end;
[ sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot];
[ exact R10 | rewrite R9, Z.add_0_r, (YN3e.ews4 sp argv envp Hsp Hva Hve uid hw rnd), (YN3e.ews5 sp argv envp Hsp Hva Hve uid hw rnd); apply (f_equal (Z_to_bv 64)); lia ]
| ].
all: clear H9 Hnz Hz Hnw R10 R9 Rfr.
all: idtac "PHASE C".
all: csym_run_to_with src0tbl_ok HS 0x141f8; clear regs1.
all: idtac "PHASE D".
all: reg_of HS (8%bv:reg) H8; reg_of HS (10%bv:reg) H10.
all: pose proof (z_argv_bounds sp argv envp 0 ltac:(lia)) as B0.
all: lazymatch goal with |- crealizes _ (mkCfg ?ms _) _ =>
destruct (src0_progname_scan (nth 0 argv []) _ (ms_mem ms) (seg_rom src0segs) (ms_regs ms)
(argv_no_nul argv Hva 0 ltac:(lia))
ltac:(rewrite (YN3e.ews1 sp argv envp Hsp Hva Hve uid hw rnd); lia)
ltac:(left; rewrite (YN3e.ews1 sp argv envp Hsp Hva Hve uid hw rnd); unfold PROGNAME; lia)
H8 H10
((YN3e.argv0_reads sp argv envp Hsp Hva Hve uid hw rnd) (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 1 _ _ HR eq_refl)))
as (regs2 & Hms & R11 & R12 & R13 & Rfr) end.
all: pose proof (st_ok_mkst src0segs _ _ _ HS eq_refl) as Hshape;
rewrite Hshape; (eapply crealizes_msteps; [exact Hh | exact Hlz | exact Hms | ]);
rewrite Hshape in HS; clear Hshape Hms.
all: lazymatch goal with |- crealizes _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes _ _ ?bs =>
lazymatch type of HS with st_ok _ ?E ?ss (mkst _ _ ?m _) =>
let rs' := eval vm_compute in (opt_mem (store_region (ss_mem ss) None 0x4ecf0 8 (CVal 8 (SOff 7 0)))) in
assert (HCB : forall i, 0 <= i < Z.of_nat (length bs) ->
cbyte src0segs E (base_val E None + 0x4ecf0) (CVal 8 (SOff 7 0)) i = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite length_N_to_le_bytes in Hi;
change (CVal 8 (SOff 7 0)) with (CVal (N.of_nat 8) (SOff 7 0));
rewrite (st_bytes_cbyte src0segs E) by lia;
unfold word_to_le_bytes; rewrite Z_to_le_bytes_st; do 2 f_equal;
cbn [sv_denot]; rewrite Z.add_0_r, (YN3e.ews7 sp argv envp Hsp Hva Hve uid hw rnd), (YN3e.ews1 sp argv envp Hsp Hva Hve uid hw rnd); reflexivity
| ];
pose proof (proj2 (swrite_sound src0segs E m (ss_mem ss) None 0x4ecf0 (CVal 8 (SOff 7 0)) bs rs'
(st_ok_mem_ok src0segs E ss _ HS)
ltac:(rewrite length_N_to_le_bytes; vm_compute; reflexivity)
ltac:(rewrite length_N_to_le_bytes; lia)
ltac:(rewrite length_N_to_le_bytes; reflexivity) HCB)) as HM;
change (mem_ok src0segs E m' rs') in HM;
unshelve epose proof (st_ok_set_regs_mem src0segs 9%nat E E ss _ regs2 _ 0x1421c m m' rs' upd_progname
HS (env_agree_refl 9%nat E) _ _ _ _ HM) as HS';
[ vm_compute; reflexivity
| reflexivity
| sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot];
[ rewrite R11, Z.add_0_r, (YN3e.ews2 sp argv envp Hsp Hva Hve uid hw rnd), (YN3e.ews1 sp argv envp Hsp Hva Hve uid hw rnd); reflexivity | exact R12 | exact R13 ]
| clear HS HM HCB; rename HS' into HS;
apply (runs_at_wbytes_below (bv_unsigned sp) m _ (Z_to_bv 64 PROGNAME) bs) in HR;
[ | rewrite length_N_to_le_bytes; change (bv_unsigned (Z_to_bv 64 PROGNAME)) with PROGNAME;
unfold PROGNAME; lia ] ]
end end end.
all: clear H8 H10 R11 R12 R13 Rfr.
all: sym_add_fact HS 7%nat (ptr_fact 0);
[ unfold ptr_fact, SP_LO, SP_HI, K_stack; cbn [af_lo af_hi af_al2]; rewrite (YN3e.ews7 sp argv envp Hsp Hva Hve uid hw rnd);
pose proof (progname_off_le (nth 0 argv [])); pose proof (rand_off_bound argv envp Hva Hve);
pose proof (block_fits sp argv envp Hfits) as HBF; unfold SP_HI in HBF;
change (2^0) with 1; rewrite Z.mod_1_r; lia
| ].
all: clear B0.
all: idtac "PHASE E".
all: csym_run_with src0tbl_ok HS; clear regs2.
all: idtac "PHASE F".
all: lazymatch type of HS with st_ok_ecall _ ?E ?ss _ =>
sym_ecall_open HS; cbn [ms_mem pend_at] in HR;
lazymatch goal with Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
eapply crz_set_tid_first; [exact Hh | exact Hlz | rewrite (Hregs 17%bv); reflexivity | exact Htid | ];
intros tid Htid8; rewrite PID_MAX_ENVELOPE_val in Htid8;
assert (HA8 : env_agree 8%nat E (E_st sp argv envp uid hw rnd tid))
by (split; [intros n Hn; do 8 (destruct n as [|n]; [reflexivity|]); lia | reflexivity]);
pose proof (st_ok_resume_mem src0segs 8%nat E (E_st sp argv envp uid hw rnd tid) ss regs mem (SOff 8 0) tid (ss_mem ss)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))
Hregs HA8 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)
(mem_ok_agree src0segs 8%nat _ _ mem (ss_mem ss) HA8 ltac:(vm_compute; reflexivity) Hmem)
(facts_ok_add_atom _ _ 8%nat tid_fact
(facts_ok_agree 8%nat _ _ (ss_facts ss) HA8 ltac:(vm_compute; reflexivity) HG)
ltac:(unfold afact_ok, tid_fact; cbn [af_lo af_hi af_al2]; rewrite (YN3e.ews8 sp argv envp uid hw rnd);
change (2^0) with 1; rewrite Z.mod_1_r; lia))) as HS;
clear Hregs Hmem HG HA8; sym_norm HS;
assert (Hh' : m_halted (with_tid tid model) = None) by exact Hh;
assert (Hlz' : m_vm_lazy (with_tid tid model) = []) by exact Hlz
end
end.
all: idtac "PHASE G".
all: csym_run_to_with src0tbl_ok HS 0x14a30.
all: sym_add_chunk_sem HS (@None nat) guard_data_chunk;
[ intros HCS; apply (guard_data_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM);
[ cbn; lia
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS) ]
| ].
all: csym_run_to_with src0tbl_ok HS 0x14a34.
all: sym_add_chunk_sem HS (@None nat) canary_chunk;
[ intros HCS; apply (canary_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM CANARY_ATOM);
[ cbn; lia
| reflexivity
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS)
| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HCS))) ]
| ].
all: idtac "PHASE H".
all: csym_run_to_with src0tbl_ok HS 0x12828.
all: idtac "PHASE I".
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_head src0segs E ss ms keep_zero) in HS;
apply (st_ok_prune src0segs E _ ms [] [0%nat]) in HS end.
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_all src0segs E ss ms keep_main) in HS;
apply (st_ok_agree_pd src0segs (fun _ => true) (not_in [UID_DATOM; HWCAP_DATOM]) _ (E_main sp argv envp tid rnd)) in HS;
[ | apply E_st_main_agree | vm_compute; reflexivity ] end.
all: sym_norm HS.
- change (st_ok src0segs (E_main sp argv envp tid rnd) (ss_main true) ms) in HS. exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp argv envp tid rnd) (ss_main false) ms) in HS. exact (K ms tid Htid8 HS HR).
Qed.
End f.
Theorem src0_start_cf : forall (two : bool) sp brk mbase rnd lim inp T,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
(if two then (2 <= length (in_argv inp))%nat else True) ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src0segs (E_main sp (in_argv inp) (in_envp inp) tid rnd) (ss_main two) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp (in_argv inp) (in_envp inp) rnd) ->
crealizes src0_msyms (mkCfg ms (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp))) T) ->
crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) T.
Proof.
intros two sp brk mbase rnd lim inp T Hsp Hva Hve Hfits Htwo K.
unfold init_config.
apply (src0_start_gen_cf sp (in_argv inp) (in_envp inp) Hsp Hva Hve Hfits (in_uid inp) (in_hwcap inp) rnd two);
[exact Htwo | reflexivity | reflexivity | reflexivity | exact K].
Qed.
