(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the driver states up to the first malloc indexed by the run's CONFIG_RSEQ flag, the auxv region dropped at that call so one post state serves both flags, a flag-free open-failure state ss_open_c, the models taking the entry draw's vDSO, the initial-ledger lemmas vdso_rx_gap and init_ledger, E_m1 over the run, and the lfeed tactic). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0o YK0q YQ0k YN06 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH05 YH07 YH06 YO3p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YL05 YL01 YL06 YL0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05 YK0a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
(* Feeds a section lemma its non-dependent premises (the launch hypotheses
   valid_sp, valid_argv, ..., entry_launch_ok_va) from the context, so call
   sites need not spell out which of them a lemma's section abstracted. *)
Ltac lfeed H :=
repeat match type of H with ?A -> _ =>
let a := fresh "a" in assert (a : A) by (first [assumption | lia]); specialize (H a); clear a end.
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
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Lemma src2_segs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x60000) src2segs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma runs_at_mbyte : forall spv m m' l,
0x60000 <= spv ->
(forall a, spv <= a -> a < 2 ^ 64 -> mbyte src2segs m' a = mbyte src2segs m a) ->
runs_at spv m l -> runs_at spv m' l.
Proof.
intros spv m m' l Hsp Hmb HR. unfold runs_at in *. rewrite Forall_forall in HR |- *.
intros [a bs] Hin. destruct (HR _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
split; [exact H1|]. split; [exact H2|]. intros j Hj.
specialize (H3 j Hj). specialize (Hmb (a + Z.of_nat j) ltac:(lia) ltac:(lia)).
unfold mbyte in Hmb.
rewrite (seg_rom_above src2segs 0x60000 _ src2_segs_top) in Hmb by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); rewrite Z.mod_small by lia; lia).
rewrite H3 in Hmb. destruct (m' (Z_to_bv 64 (a + Z.of_nat j))); destruct (nth_error bs j); cbn in Hmb; congruence.
Qed.
(* 727298f3: [init_config] installs the launch's vDSO draw into the initial
   model ([with_vdso (vdso_run_init (ed_vdso rnd))], Run.v), so the models
   take the entry draw. *)
Definition MD0 (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw) : Model :=
with_tid tid (with_vdso (vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved src2segs) brk mbase sp lim inp)).
Definition MD_file (path : list byte) (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw) : Model :=
with_fds (fd_insert (m_fds (MD0 tid brk mbase sp lim inp rnd)) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0)))
(MD0 tid brk mbase sp lim inp rnd).
Definition MD_dir (tid brk mbase sp : word) (lim : Z) (inp : ProcInput) (rnd : EntryDraw) : Model :=
with_fds (fd_insert (m_fds (MD0 tid brk mbase sp lim inp rnd)) (Z_to_bv 64 3) FdDir) (MD0 tid brk mbase sp lim inp rnd).
Lemma MD0_fds : forall tid brk mbase sp lim inp rnd,
m_fds (MD0 tid brk mbase sp lim inp rnd) =
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Proof. intros. unfold MD0, init_model. autorewrite with model. reflexivity. Qed.
Lemma MD0_fs : forall tid brk mbase sp lim inp rnd, m_fs (MD0 tid brk mbase sp lim inp rnd) = in_fs inp.
Proof. intros. unfold MD0, init_model. autorewrite with model. reflexivity. Qed.
(* The launch's vDSO pair ([State.init_reserved]) sits just below
   [page_round_down_Z (min mbase (sp - stack_max_size))], far above the break:
   the break is within 1 GiB of the image, the mmap base is at least
   [mmap_base_min].  The three pages are what the first brk grow's region
   test asks for at 727298f3: the grown pages and one guard page
   ([Mmap.brk_grow_ok]). *)
Lemma vdso_rx_gap : forall kb brk mbase sp, valid_sp sp -> valid_brk src2segs brk -> valid_mmap_base mbase ->
Forall (fun e => bv_unsigned brk + 3 * 4096 <= bv_unsigned (fst e) /\ 0 < bv_unsigned (snd e) <= 0x14000)
(vdso_reserved kb (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))).
Proof.
intros kb brk mbase sp (S1 & S2 & _) (B1 & B2 & _) (M1 & M2 & _).
let v := eval vm_compute in (reserved_top (segments_reserved src2segs)) in
change (reserved_top (segments_reserved src2segs)) with v in B2.
unfold sp_window_lo, sp_window_hi in S1, S2. unfold mmap_base_min in M1. unfold mmap_base_max, sp_window_hi in M2.
unfold brk_aslr_max in B2.
set (z := Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
assert (Hz : 0x154555557000 <= z <= 0x800000000000) by (unfold z, stack_max_size; lia).
assert (Ht : z - 4096 < page_round_down_Z z <= z).
{ unfold page_round_down_Z, page_size. pose proof (Z.div_mod z 4096 ltac:(lia)). pose proof (Z.mod_pos_bound z 4096 ltac:(lia)). lia. }
pose proof (vdso_len_bounds kb) as VL. unfold page_size in VL.
pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
apply Forall_forall. intros [a n] Hin. cbn [fst snd].
pose proof (vdso_reserved_above kb (page_round_down_Z z) a n ltac:(unfold two_pow_64; lia) Hin) as [H1 H2].
split; [lia|].
revert Hin. unfold vdso_reserved. cbv zeta. destruct (Z.ltb _ _); [intros []|].
intros [E|[E|[]]]; injection E as <- <-;
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); unfold vdso_vvar_pages, page_size;
rewrite Z.mod_small by lia; lia.
Qed.
(* The four facts the first malloc ([YL0j.src2_malloc1]) asks of the initial
   ledger, for any model whose ledger and kernel are the launch's. *)
Lemma init_ledger : forall md brk mbase sp lim inp,
m_vmmaps md = m_vmmaps (init_model (segments_reserved src2segs) brk mbase sp lim inp) ->
m_kernel md = in_kernel inp ->
valid_sp sp -> valid_brk src2segs brk -> valid_mmap_base mbase ->
exists rx, m_vmmaps md = mkVmMapsFull (segments_reserved src2segs ++ rx) [] [] brk brk lim mbase sp
/\ Forall (fun e => bv_unsigned brk + 3 * 4096 <= bv_unsigned (fst e) /\ 0 < bv_unsigned (snd e) <= 0x14000) rx
/\ (length rx <= 2)%nat
/\ incl (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md))) (vm_reserved (m_vmmaps md)).
Proof.
intros md brk mbase sp lim inp Hvm Hk Hsp Hbrk Hmb.
exists (vdso_reserved (in_kernel inp) (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))).
split; [rewrite Hvm; reflexivity|].
split; [apply vdso_rx_gap; assumption|].
split; [unfold vdso_reserved; cbv zeta; destruct (Z.ltb _ _); cbn; lia|].
rewrite Hk, Hvm, vm_reserved_init_model. apply incl_appr, incl_refl.
Qed.
Definition src2_keep : ivl := Eval vm_compute in (drv_keep src2_msyms).


Definition RS_LO : Z := src2_D_read_stage.
Definition RS_HI : Z := src2_D_read_stage + 65536.
Definition TDCAN_LO : Z := src2_tp - 16.
Definition TDCAN_HI : Z := src2_tp - 8.
Definition cut_win (lo hi : Z) (x : nat * YQ0b.region) : nat * YQ0b.region :=
let r := snd x in
match r_base r with
| None => if (r_lo r <? hi) && (lo <? r_hi r) then (fst x, with_chunks r (cut_chunks lo hi (r_chunks r))) else x
| Some _ => x
end.
Definition split_win (lo hi : Z) (x : nat * YQ0b.region) : list (nat * YQ0b.region) :=
let r := snd x in
match r_base r with
| None => if (r_lo r <=? lo) && (hi <=? r_hi r)
then [ (fst x, carve r (r_lo r) lo (Z.max (r_wlo r) (r_lo r)) (Z.min (r_whi r) lo));
(fst x, YQ0b.mkRegion None lo hi 0 0 []);
(fst x, carve r hi (r_hi r) (Z.max (r_wlo r) hi) (Z.min (r_whi r) (r_hi r))) ]
else [x]
| Some _ => [x]
end.
(* #38: [ss_main two rs] is indexed by the run's CONFIG_RSEQ flag [rs] as well
   (YO3p.v): the flag makes the entry stack's auxv block two pairs longer.  The
   two states differ ONLY in that region (atom 5, bytes 0..464 against 0..432),
   and they disagree in VALUE from byte 416 on, where the rseq-off vector has
   its AT_NULL pair; so no common weakening keeps the whole vector, and the
   malloc site below needs the whole vector: musl's [get_random_secret] reads
   every key up to AT_NULL ([auxv_check]/[YP0c.auxv_pre]).  So the states up
   to the first malloc are kept per flag, and the auxv region is dropped from
   the layout at that call ([drop_auxv]), after which the two runs are the same
   state ([post_m1]).  Only the argc = 2 path ([two] = true) reaches here. *)
Definition drv_lay (rs : bool) : list (nat * YQ0b.region) :=
map (cut_win TDCAN_LO TDCAN_HI) (flat_map (split_win RS_LO RS_HI) (drv_relayout src2_msyms (ss_mem (ss_main true rs)))).
Definition drv_state (rs : bool) : sstate :=
mkSS (ss_pc (ss_main true rs)) (ss_regs (ss_main true rs)) (map snd (drv_lay rs)) (ss_resv (ss_main true rs)) (ss_facts (ss_main true rs)).
Definition ss_drv_t : sstate := Eval vm_compute in (drv_state true).
Definition ss_drv_f : sstate := Eval vm_compute in (drv_state false).
Definition ss_drv (rs : bool) : sstate := if rs then ss_drv_t else ss_drv_f.
Lemma st_ok_drv : forall rs E ms, st_ok src2segs E (ss_main true rs) ms -> st_ok src2segs E (ss_drv rs) ms.
Proof.
intros [|] E ms HS.
- exact (st_ok_relayout src2segs E ss_main_tt ms (drv_lay true) HS ltac:(vm_compute; reflexivity)).
- exact (st_ok_relayout src2segs E ss_main_tf ms (drv_lay false) HS ltac:(vm_compute; reflexivity)).
Qed.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src2segs src2tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src2segs src2tbl FUEL pc ss).
Definition ss_open_t : sstate := Eval vm_compute in (run_ (add_cond ss_drv_t (mkAC BC_EQ (SOff 3 0) (SLit 2)))).
Definition ss_open_f : sstate := Eval vm_compute in (run_ (add_cond ss_drv_f (mkAC BC_EQ (SOff 3 0) (SLit 2)))).
Definition ss_open (rs : bool) : sstate := if rs then ss_open_t else ss_open_f.
(* The open-FAILURE arm never reaches malloc, so it needs no auxv vector:
   [ss_open_c] is the open state with the auxv region dropped, the same state
   for both flags, and every failure path is proved once from it. *)
Definition drop_auxv_mem (m : smem) : list (nat * YQ0b.region) :=
filter (fun p => negb (obase_eqb (r_base (snd p)) (Some 5%nat) && (r_lo (snd p) =? 0))) (combine (seq 0 (length m)) m).
Definition L_open : list (nat * YQ0b.region) := Eval vm_compute in (drop_auxv_mem (ss_mem ss_open_t)).
Definition ss_open_c : sstate := Eval vm_compute in
(mkSS (ss_pc ss_open_t) (ss_regs ss_open_t) (map snd L_open) (ss_resv ss_open_t) (ss_facts ss_open_t)).
Lemma open_c_ok : forall rs E regs mem,
regs_ok E (ss_regs (ss_open rs)) regs -> mem_ok src2segs E mem (ss_mem (ss_open rs)) -> facts_ok E (ss_facts (ss_open rs)) ->
regs_ok E (ss_regs ss_open_c) regs /\ mem_ok src2segs E mem (ss_mem ss_open_c) /\ facts_ok E (ss_facts ss_open_c)
/\ ss_pc (ss_open rs) = ss_pc ss_open_c.
Proof.
intros rs E regs mem Hr Hm Hg.
replace (ss_regs ss_open_c) with (ss_regs (ss_open rs)) by (destruct rs; vm_compute; reflexivity).
replace (ss_facts ss_open_c) with (ss_facts (ss_open rs)) by (destruct rs; vm_compute; reflexivity).
replace (ss_pc ss_open_c) with (ss_pc (ss_open rs)) by (destruct rs; vm_compute; reflexivity).
replace (ss_mem ss_open_c) with (map snd L_open) by (vm_compute; reflexivity).
split; [exact Hr|]. split; [|split; [exact Hg | reflexivity]].
apply (mem_ok_relayout src2segs E mem (ss_mem (ss_open rs)) L_open Hm).
destruct rs; vm_compute; reflexivity.
Qed.
Definition ss_m1_t : sstate := Eval vm_compute in
(runto_ src2_A_malloc (resume ss_open_t (SLit 3) (ss_mem ss_open_t) (ss_facts ss_open_t))).
Definition ss_m1_f : sstate := Eval vm_compute in
(runto_ src2_A_malloc (resume ss_open_f (SLit 3) (ss_mem ss_open_f) (ss_facts ss_open_f))).
Definition ss_m1 (rs : bool) : sstate := if rs then ss_m1_t else ss_m1_f.
Definition MAIN_SP : Z := -128.
Definition K_M1 : nat := 10.
Definition A_BUF : nat := 14.
Definition G_M1 : nat := 26.
Definition drop_auxv (l : list (nat * YQ0b.region)) : list (nat * YQ0b.region) :=
filter (fun p => negb (obase_eqb (r_base (snd p)) (Some 5%nat) && (r_lo (snd p) =? 0))) l.
Definition L_m1 : list (nat * YQ0b.region) := Eval vm_compute in
(drop_auxv (precall src2_keep MAIN_SP ALLOC_STACK (ss_mem ss_m1_t))).
Definition RS_m1 : smem := Eval vm_compute in
(match drv_add_statics src2_msyms (map snd L_m1) G_M1 with Some x => x | None => [] end).
Definition RA_m1 : Z := Eval vm_compute in (src2_A_main + 0x54).
Lemma site_m1 : forall rs, site_check src2_msyms (ss_m1 rs) src2_A_malloc RA_m1 MAIN_SP src2_keep [] K_M1 L_m1 = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma statics_m1 : drv_add_statics src2_msyms (map snd L_m1) (K_M1 + 16) = Some RS_m1.
Proof. vm_compute. reflexivity. Qed.
Lemma pristine_m1 : forall rs, pristine_check src2_msyms (ss_mem (ss_m1 rs)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma auxv_m1 : forall rs, auxv_check src2_msyms (APC.rseq_z rs) (ss_mem (ss_m1 rs)) (ss_facts (ss_m1 rs)) 5 6 = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition ss_m1_post : sstate := Eval vm_compute in (post_state ss_m1_t RA_m1 K_M1 RS_m1).
Lemma post_m1 : forall rs, post_state (ss_m1 rs) RA_m1 K_M1 RS_m1 = ss_m1_post.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition ss_m1_null : sstate := Eval vm_compute in
(mkSS (ss_pc ss_m1_post) (sr_set (ss_regs ss_m1_post) 10%bv (SLit 0)) (ss_mem ss_m1_post) (ss_resv ss_m1_post) (ss_facts ss_m1_post)).
(* [E_main] takes the run [inp] and its execfn string (YO3p.v); the execfn is
   [in_execfn inp] at every call site, so it is read off [inp] here. *)
Definition E_m1 (sp tid : word) (inp : ProcInput) (argv envp : list (list byte)) (rnd : EntryDraw) (regs' : bvmap 5 word) (g : Z) : env :=
post_env (E_main sp inp argv envp (in_execfn inp) tid rnd) K_M1 regs' g.
Definition blk_fact : afact := mkAF 4096 CEIL_MAX 4.
Definition ss_m1_ok : sstate := Eval vm_compute in (add_atom ss_m1_post A_BUF blk_fact).
Definition ss_rd1 : sstate := Eval vm_compute in (run_ ss_m1_ok).
Definition ss_rderr : sstate := Eval vm_compute in (resume ss_rd1 (SLit (2 ^ 64 - 21)) (ss_mem ss_rd1) (ss_facts ss_rd1)).
Lemma ss_rd1_facts :
ss_pc ss_rd1 = src2_A_syscall_cp_c + 0x1c /\ sr_get (ss_regs ss_rd1) 17%bv = SLit 63 /\ sr_get (ss_regs ss_rd1) 10%bv = SLit 3 /\
sr_get (ss_regs ss_rd1) 11%bv = SLit RS_LO /\ sr_get (ss_regs ss_rd1) 12%bv = SLit 65536 /\ ss_resv ss_rd1 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
End b.
