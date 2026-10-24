(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac at_node k :=
lazymatch goal with
| Hregs : regs_ok ?E ?sr _, Hmem : mem_ok _ _ _ ?rs, HG : facts_ok _ ?G
|- realizes _ (mkCfg (mkst (regupd _ 10 ?RET) (v_addi (Z_to_bv 64 ?pc) 4) _ _) _) _ =>
k E (mkSS pc sr rs (@None sv) G) RET
end.
Ltac resume_sv segs rv :=
at_node ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_sv segs E ss regs mem rv RET Hregs Hmem HG _) as H;
[ | clear Hregs Hmem HG; sym_norm H ]
end).
Ltac resume_atom segs n f :=
at_node ltac:(fun E ss RET =>
lazymatch goal with
| Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
let H := fresh "HS" in
unshelve epose proof (st_ok_resume_atom segs n f E ss regs mem RET Hregs Hmem HG
ltac:(vm_compute; reflexivity) _ _ _) as H;
[ | | | clear Hregs Hmem HG; sym_norm H ]
end).
Ltac drv_run_with tblok HS HF :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
lazymatch st with
| RS_ecall =>
eapply (rz_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_stopped ?why =>
eapply (rz_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_running =>
eapply (rz_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
end
end
end
end.
Ltac drv_run_to_with tblok HS stop HF :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in
lazymatch st with
| RS_ecall =>
eapply (rz_run_to_ecall segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_stopped ?why =>
eapply (rz_run_to_stop segs tbl tblok FUEL stop E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
| RS_running =>
eapply (rz_run_to_running segs tbl tblok FUEL stop E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
cbn [ms_mem mkst pend_at] in HF
end
end
end
end.
Ltac drv_runs E ss0 HS HF HR :=
lazymatch type of HS with
| st_ok ?segs _ ?ss' ?msn =>
eapply (runs_at_after segs E ss' msn (ss_mem ss0)) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
| st_ok_ecall ?segs _ ?ss' ?msn =>
eapply (runs_at_after_ecall segs E ss' msn (ss_mem ss0)) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
end.
Ltac drv_runs' E HS HF HR :=
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
lazymatch type of HS with
| st_ok ?segs _ ?ss' ?msn =>
eapply (runs_at_after segs E ss' msn rs0) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
| st_ok_ecall ?segs _ ?ss' ?msn =>
eapply (runs_at_after_ecall segs E ss' msn rs0) in HR;
[| exact HS | vm_compute; reflexivity | exact HF | cbn; lia ]
end end.
Ltac drv_anch := assumption.
Ltac drv_mr mraf keep E HS HF HMR :=
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
let G := lazymatch type of HS with st_ok _ _ ?ss' _ => constr:(ss_facts ss') | st_ok_ecall _ _ ?ss' _ => constr:(ss_facts ss') end in
let HG0 := fresh "HG0" in
assert (HG0 : facts_ok E G) by (lazymatch type of HS with
| st_ok _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X
| st_ok_ecall _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X end);
let HSA0 := fresh "HSA0" in
assert (HSA0 : stack_anchored E G) by drv_anch;
apply (mraf _ _ _ _ _ E G keep rs0 HMR HG0 HSA0 ltac:(vm_compute; reflexivity)) in HF;
clear HMR HG0 HSA0; rename HF into HMR
end.
Ltac model_facts M Hh Hlz :=
assert (Hh : m_halted M = None) by (autorewrite with model; reflexivity);
assert (Hlz : m_vm_lazy M = []) by (autorewrite with model; reflexivity).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma find_segment_above : forall (sl : list Segment) top a n,
forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sl = true ->
top <= a -> 0 < n -> find_segment sl a n = None.
Proof.
induction sl as [|sg rest IH]; intros top a n Hall Ha Hn; cbn [find_segment]; [reflexivity|].
cbn [forallb] in Hall. apply andb_prop in Hall as [H1 H2]. apply Z.leb_le in H1.
destruct (Z.leb_spec (Z.of_N (seg_base sg)) a); cbn [andb];
[ destruct (Z.leb_spec (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); [lia|] |];
eapply IH; eauto.
Qed.
Lemma seg_rom_above : forall segs top (a : word),
forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true ->
top <= bv_unsigned a -> seg_rom segs a = None.
Proof.
intros segs top a Hall Ha. unfold seg_rom, memory_read.
rewrite (find_segment_above segs top) by (try exact Hall; lia). reflexivity.
Qed.
Lemma src0_segs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x60000) src0segs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma runs_at_mbyte : forall spv m m' l,
0x60000 <= spv ->
(forall a, spv <= a -> a < 2 ^ 64 -> mbyte src0segs m' a = mbyte src0segs m a) ->
runs_at spv m l -> runs_at spv m' l.
Proof.
intros spv m m' l Hsp Hmb HR. unfold runs_at in *. rewrite Forall_forall in HR |- *.
intros [a bs] Hin. destruct (HR _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
split; [exact H1|]. split; [exact H2|]. intros j Hj.
specialize (H3 j Hj). specialize (Hmb (a + Z.of_nat j) ltac:(lia) ltac:(lia)).
unfold mbyte in Hmb.
rewrite (seg_rom_above src0segs 0x60000 _ src0_segs_top) in Hmb by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); rewrite Z.mod_small by lia; lia).
rewrite H3 in Hmb. destruct (m' (Z_to_bv 64 (a + Z.of_nat j))); destruct (nth_error bs j); cbn in Hmb; congruence.
Qed.
Definition MD0 (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) : Model :=
with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp).
Definition MD_file (path : list byte) (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) : Model :=
with_fds (fd_insert (m_fds (MD0 tid brk mbase sp lim inp)) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)))
(MD0 tid brk mbase sp lim inp).
Definition MD_dir (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) : Model :=
with_fds (fd_insert (m_fds (MD0 tid brk mbase sp lim inp)) (Z_to_bv 64 3) FdDir) (MD0 tid brk mbase sp lim inp).
Lemma MD0_fds : forall tid brk mbase sp lim inp,
m_fds (MD0 tid brk mbase sp lim inp) =
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Proof. intros. unfold MD0, init_model. autorewrite with model. reflexivity. Qed.
Lemma MD0_fs : forall tid brk mbase sp lim inp, m_fs (MD0 tid brk mbase sp lim inp) = in_fs inp.
Proof. intros. unfold MD0, init_model. autorewrite with model. reflexivity. Qed.
Definition src0_keep : ivl := Eval vm_compute in (drv_keep src0_msyms).
Lemma src0_keep_check : keep_check src0_msyms src0_keep = true.
Proof. vm_compute. reflexivity. Qed.
Lemma src0_errno_check : errno_check src0_msyms = true.
Proof. vm_compute. reflexivity. Qed.
Definition RS_LO : Z := src0_D_read_stage.
Definition RS_HI : Z := src0_D_read_stage + 65536.
Definition TDCAN_LO : Z := src0_tp - 16.
Definition TDCAN_HI : Z := src0_tp - 8.
Definition cut_win (lo hi : Z) (x : nat * YP09.region) : nat * YP09.region :=
let r := snd x in
match r_base r with
| None => if (r_lo r <? hi) && (lo <? r_hi r) then (fst x, with_chunks r (cut_chunks lo hi (r_chunks r))) else x
| Some _ => x
end.
Definition split_win (lo hi : Z) (x : nat * YP09.region) : list (nat * YP09.region) :=
let r := snd x in
match r_base r with
| None => if (r_lo r <=? lo) && (hi <=? r_hi r)
then [ (fst x, carve r (r_lo r) lo (Z.max (r_wlo r) (r_lo r)) (Z.min (r_whi r) lo));
(fst x, YP09.mkRegion None lo hi 0 0 []);
(fst x, carve r hi (r_hi r) (Z.max (r_wlo r) hi) (Z.min (r_whi r) (r_hi r))) ]
else [x]
| Some _ => [x]
end.
Definition drv_lay (two : bool) : list (nat * YP09.region) :=
map (cut_win TDCAN_LO TDCAN_HI) (flat_map (split_win RS_LO RS_HI) (drv_relayout src0_msyms (ss_mem (ss_main two)))).
Definition drv_state (two : bool) : sstate :=
mkSS (ss_pc (ss_main two)) (ss_regs (ss_main two)) (map snd (drv_lay two)) (ss_resv (ss_main two)) (ss_facts (ss_main two)).
Definition ss_drv_t : sstate := Eval vm_compute in (drv_state true).
Definition ss_drv_f : sstate := Eval vm_compute in (drv_state false).
Definition ss_drv (two : bool) : sstate := if two then ss_drv_t else ss_drv_f.
Lemma st_ok_drv : forall two E ms, st_ok src0segs E (ss_main two) ms -> st_ok src0segs E (ss_drv two) ms.
Proof.
intros [|] E ms HS.
- exact (st_ok_relayout src0segs E ss_main_t ms (drv_lay true) HS ltac:(vm_compute; reflexivity)).
- exact (st_ok_relayout src0segs E ss_main_f ms (drv_lay false) HS ltac:(vm_compute; reflexivity)).
Qed.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src0segs src0tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL pc ss).
Definition ss_open : sstate := Eval vm_compute in (run_ (add_cond ss_drv_t (mkAC BC_EQ (SOff 3 0) (SLit 2)))).
Definition ss_m1 : sstate := Eval vm_compute in
(runto_ src0_A_malloc (resume ss_open (SLit 3) (ss_mem ss_open) (ss_facts ss_open))).
Definition MAIN_SP : Z := -128.
Definition K_M1 : nat := 10.
Definition A_BUF : nat := 14.
Definition G_M1 : nat := 26.
Definition L_m1 : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep MAIN_SP ALLOC_STACK (ss_mem ss_m1)).
Definition RS_m1 : smem := Eval vm_compute in
(match drv_add_statics src0_msyms (map snd L_m1) G_M1 with Some x => x | None => [] end).
Definition RA_m1 : Z := Eval vm_compute in (src0_A_main + 0x54).
Lemma site_m1 : site_check src0_msyms ss_m1 src0_A_malloc RA_m1 MAIN_SP src0_keep [] K_M1 L_m1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma statics_m1 : drv_add_statics src0_msyms (map snd L_m1) (K_M1 + 16) = Some RS_m1.
Proof. vm_compute. reflexivity. Qed.
Lemma pristine_m1 : pristine_check src0_msyms (ss_mem ss_m1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma auxv_m1 : auxv_check src0_msyms (ss_mem ss_m1) (ss_facts ss_m1) 5 6 = true.
Proof. vm_compute. reflexivity. Qed.
Definition ss_m1_post : sstate := Eval vm_compute in (post_state ss_m1 RA_m1 K_M1 RS_m1).
Definition ss_m1_null : sstate := Eval vm_compute in
(mkSS (ss_pc ss_m1_post) (sr_set (ss_regs ss_m1_post) 10%bv (SLit 0)) (ss_mem ss_m1_post) (ss_resv ss_m1_post) (ss_facts ss_m1_post)).
Definition E_m1 (sp tid : word) (argv envp : list (list byte)) (rnd : EntryDraw) (regs' : bvmap 5 word) (g : Z) : env :=
post_env (E_main sp argv envp tid rnd) K_M1 regs' g.
Definition blk_fact : afact := mkAF 4096 CEIL_MAX 4.
Definition ss_m1_ok : sstate := Eval vm_compute in (add_atom ss_m1_post A_BUF blk_fact).
Definition ss_rd1 : sstate := Eval vm_compute in (run_ ss_m1_ok).
Definition ss_rderr : sstate := Eval vm_compute in (resume ss_rd1 (SLit (2 ^ 64 - 21)) (ss_mem ss_rd1) (ss_facts ss_rd1)).
Lemma ss_rd1_facts :
ss_pc ss_rd1 = src0_A_syscall_cp_c + 0x1c /\ sr_get (ss_regs ss_rd1) 17%bv = SLit 63 /\ sr_get (ss_regs ss_rd1) 10%bv = SLit 3 /\
sr_get (ss_regs ss_rd1) 11%bv = SLit RS_LO /\ sr_get (ss_regs ss_rd1) 12%bv = SLit 65536 /\ ss_resv ss_rd1 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma stations_pc : ss_pc ss_m1 = src0_A_malloc /\ ss_pc ss_m1_post = RA_m1.
Proof. vm_compute. split; reflexivity. Qed.
End b.
