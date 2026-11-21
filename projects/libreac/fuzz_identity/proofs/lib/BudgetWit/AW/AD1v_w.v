(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD1v.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1v.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed B, ELV, argv_str_fits', argv_over_read, cannot_open_tfa, file_arm_tfa and 4 more; added argv_str_fits); the channel reader that fdchan asks for at LPS 727298f3 carried beside the descriptor fact, from cs_ok's co_rdr. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit Require Import MroomB.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD1u_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
(* [YP08.E0] is TOP-anchored and launch-indexed at 75d69e00 (YP08.v:209-210): entry-draw top,
   the run's own [kb_rseq] flag, and the execfn.  Every Prop below therefore carries the draw.
   Shape copied from the in-tree ported donor YL0p.v:39-45 / YL0q.v Section b: binders
   [sp brk mbase] .. [inp] .. [a0 p] .. [rnd], premises
   [valid_sp; in_argv =; valid_argv (in_argv inp); valid_envp; valid_launch;
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp; valid_input].
   [entry_stack_fits] is DROPPED rather than kept: it survives at 75d69e00 as
   [valid_entry_sv48]'s fourth conjunct, but [entry_launch_ok_va] implies it
   ([entry_launch_ok_va_fits], 75d69e00 Run.v:3718-3722), so carrying both is redundant.
   MEASURED: no prover of these Props consumes [entry_stack_fits] as a fact -- every [Hfit]
   there is either passed straight on to another Prop of this family or handed to
   [argv_str_fits'], whose premise at this revision is [bv_unsigned top <= kHighMemEnd]
   (AD1v_w.v:77-78), not [entry_stack_fits].  Firing control for that zero: the same query
   does fire on AD2i_w.v:264 and AD2i_w.v:754, two genuine direct consumptions, in a section
   that is not one of these Props. *)
#[local] Notation ELV sp rnd a0 p inp xw xd :=
(YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) [a0; p] (in_envp inp) (in_execfn inp) xw xd).
Definition top_ok (usp : Z) (ly : alayout) : Prop :=
usp - 160 <= ly_top ly <= usp + 3920 /\ ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd
/\ YM05.ceil_of_top (usp - stack_max_size).

Lemma top_ok_le : forall usp n ly ly', layout_le n ly ly' -> top_ok usp ly -> top_ok usp ly'.
Proof.
intros usp n ly ly' (_ & _ & _ & _ & _ & _ & _ & _ & Et & Elo & Ehi & _) (H1 & H2 & H3 & H4).
unfold top_ok. rewrite Et, Elo, Ehi. exact (conj H1 (conj H2 (conj H3 H4))).
Qed.
Lemma top_ok_ceil : forall usp ly, top_ok usp ly -> YM05.ceil_of_top (usp - stack_max_size).
Proof. intros usp ly (_ & _ & _ & H). exact H. Qed.

Lemma finv_run : forall ly S (W : world tfibsegs) mem0 md (H : word -> bool) E rs (m m' : word -> option byte) usp,
AR tfibsegs B ly S W mem0 md -> frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb AD1y_w.drv_win_ok rs = true ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp -> usp <= sp_window_hi -> top_ok usp ly -> FINV ly H m -> FINV ly H m'.
Proof.
intros ly S W mem0 md H E rs m m' usp HAR HF Hok E0 Ulo Uhi (_ & Hlo & Hhi & HCT) HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_stretch B ly S W mem0 md H E rs m m' usp HAR HF Hok E0); [| | exact Ulo | exact HFI].
- rewrite Hlo. unfold ASAN_CEIL, stack_max_size in *. lia.
- rewrite Hhi. unfold kHighMemEnd, sp_window_hi in *. lia.
Qed.

Lemma finv_site : forall (HB : TfibSyms B) (ARL : AR_laws tfibsegs B) stk ly S (W : world tfibsegs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp,
AR tfibsegs B ly S W mem md -> acall_post tfibsegs B stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n)) ->
top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
FINV ly (w_H W) mem -> FINV ly' (w_H W') mem'.
Proof.
intros HB ARL stk ly S W regs mem md E ly' S' W' regs' mem' md' usp HAR HP HE (_ & Hlo & Hhi & HCT) Ulo Uhi Hsp Hstk HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_acall_post B HB ARL stk ly S W regs mem md E ly' S' W' regs' mem' md' HAR HP HE); [| | | exact HFI].
- rewrite Hlo. unfold ASAN_CEIL, stack_max_size in *. lia.
- rewrite Hhi. unfold kHighMemEnd, sp_window_hi in *. lia.
- unfold sp_window_lo in *. lia.
Qed.

Lemma finv_icpt : forall (HB : TfibSyms B) (ARL : AR_laws tfibsegs B) ly S (W : world tfibsegs) mem md (mem' : word -> option byte) (P : Z -> Prop) lo hi usp,
AR tfibsegs B ly S W mem md -> top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
usp - 65536 <= lo -> hi <= usp ->
(forall a, P a -> exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
FINV ly (w_H W) mem -> FINV ly (w_H W) mem'.
Proof.
intros HB ARL ly S W mem md mem' P lo hi usp HAR (_ & Hlo & Hhi & HCT) Ulo Uhi Hfr Hl Hh HP HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_off B ly S W mem md mem' P (fun a => lo <= a < hi) HAR Hfr); [|exact HFI].
intros a Ha. split.
- intros HPa. destruct (HP a HPa) as (p0 & n0 & Hin & Hpa). exact (finv_avoids_block B ARL ly S W mem md p0 n0 a HAR Hin Ha Hpa).
- apply (finv_avoids_stack B ly S W mem md lo hi a HAR); [| | | exact Ha].
+ rewrite Hlo. unfold ASAN_CEIL, stack_max_size in *. lia.
+ rewrite Hhi. unfold kHighMemEnd, sp_window_hi in *. lia.
+ unfold sp_window_lo in *. lia.
Qed.
Lemma argv_str_fits : forall (top : word) argv envp efn k, bv_unsigned top <= kHighMemEnd -> (k < length argv)%nat ->
z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv [])) + 1 <= kHighMemEnd.
Proof.
intros top argv envp efn k Htop Hk. pose proof (YP08.tab_firstn_nth_le argv k Hk) as T.
unfold z_argv, z_strs, launch_string_bytes. rewrite !length_flatten_strings. lia.
Qed.
Lemma argv_str_fits' : forall (top : word) argv envp efn k, bv_unsigned top <= kHighMemEnd -> (k < length argv)%nat ->
z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv [])) + 1 < kHighMemEnd.
Proof.
intros top argv envp efn k Htop Hk. pose proof (YP08.tab_firstn_nth_le argv k Hk) as T.
unfold z_argv, z_strs, launch_string_bytes. rewrite !length_flatten_strings. lia.
Qed.
Lemma argv_over_read : forall sp {top : word} argv envp {efn : list byte} (two : bool) (m : word -> option byte) k,
(k < length argv)%nat -> runs_at (bv_unsigned sp) m (runs_main_tfa two sp top argv envp efn) ->
forall a, z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv [])) < a
< z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv []))
- (z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv []))) mod 8 + 8 ->
m (Z_to_bv 64 a) <> None.
Proof.
intros sp top argv envp efn two m k Hk HR a Ha.
assert (HB : YP03.bytes_at m (z_strs (bv_unsigned top) argv envp efn) (stack_tail argv envp efn)).
{ apply (runs_at_nth _ _ _ (if two then 3 else 2)%nat _ _ HR). destruct two; reflexivity. }
set (q := z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv []))) in *.
assert (Hlen : Z.of_nat (length (stack_tail argv envp efn))
= Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp) + Z.of_nat (length efn) + 9).
{ unfold stack_tail. rewrite !length_app, !length_flatten_strings, repeat_length. cbn [length]. lia. }
pose proof (YP08.tab_firstn_nth_le argv k Hk) as T.
assert (Hlo : z_strs (bv_unsigned top) argv envp efn <= q) by (unfold q, z_argv; lia).
assert (Hhi : q + 1 <= z_strs (bv_unsigned top) argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (unfold q, z_argv; lia).
pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as D2.
replace a with (z_strs (bv_unsigned top) argv envp efn + Z.of_nat (Z.to_nat (a - z_strs (bv_unsigned top) argv envp efn))) by lia.
rewrite (HB (Z.to_nat (a - z_strs (bv_unsigned top) argv envp efn))) by lia.
destruct (nth_error _ _) eqn:Hn; [discriminate|]. apply nth_error_None in Hn. exfalso. lia.
Qed.
Definition cannot_open_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ly : alayout)
(a0 p : list byte) (rnd : EntryDraw) (e : Z),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
regs_ok (ELV sp rnd a0 p inp xw xd) (ss_regs ss_open) regs ->
mem_ok tfibsegs (ELV sp rnd a0 p inp xw xd) (mrestrict (w_H W) mem) (ss_mem ss_open) ->
facts_ok (ELV sp rnd a0 p inp xw xd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) mem)
(runs_main_tfa true sp (ed_top rnd) [a0; p] (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W mem md ->
top_ok (bv_unsigned sp) ly -> m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
(* Beside the descriptor fact: [fdchan] at LPS 727298f3 asks for the model's channel
   reader too, and the diagnostic this arm writes goes to a channel.  It travels with
   [m_fds] from the hand-off, where [cs_ok]'s [co_rdr] proves it. *)
m_channel_reader md = true ->
0 < e < 4096 ->
srealizes tfibsegs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)) md)
(diag (msg_cannot_open p) (in_fs inp)).
Definition file_arm_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p data : list byte)
(rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
valid_fs (in_fs inp) ->
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs (ELV sp rnd a0 p inp xw xd) ss_m1 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) [a0; p] (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) -> m_channel_reader md = true ->
(* Theorem Labs, 2026-11: inputs whose file is shorter than the driver's header only (the fuzz-input step). *)
dlen data < HDR_MIN ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_loaded data (in_fs inp)).
Definition dir_arm_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p : list byte)
(rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
p = dot_path ->
st_ok tfibsegs (ELV sp rnd a0 p inp xw xd) ss_m1 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) [a0; p] (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir -> m_channel_reader md = true ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_dir p (in_fs inp)).
(* Theorem Labs, 2026-11: drv_pre asks qmeter S (qtight S and mroom S, room under 16 GiB: YG0n_w.ASAN_VM_LMIN) where
   the released file asks qtight S; the released AD1i.v derived mroom from the allocator's regime at 2^39
   (YG08.mroom_of_regime), which does not hold at 16 GiB.  Each caller proves it with BudgetWit/MroomB.v. *)
Definition drv_pre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd) /\ st_nev S < EV_MAX /\
YK0s.ret_ok (getr regs 1%bv) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ ly_top ly - 4128 <= spZ regs <= ly_top ly + 32 /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
s0Z regs < alloc_ceiling /\
qmeter S                                    .

(* Theorem Labs, 2026-11: drv_minv also carries MroomB.fa_clean S (no free array mapped outside the batch class),
   the part of the meter no event count bounds. *)
Definition drv_minv (S : astate) (cap dl : Z) : Prop :=
((cap = 65536 /\ prim_pristine_except S []) \/ (2 ^ 17 <= cap <= 2 * dl /\ prim_pristine_except S [kBatchClass]))
/\ quar_bytes S <= 2 * cap /\ frames S = []
/\ qtight S /\ fa_clean S                       .

Lemma drv_minv_init : forall S dl, prim_pristine_except S [] -> quar_bytes S = 0 -> frames S = [] -> qtight S -> fa_clean S ->
drv_minv S 65536 dl.
Proof. intros S dl HP HQ HF HT HC. split; [left; split; [reflexivity | exact HP] |]. split; [rewrite HQ; lia | split; [exact HF | exact (conj HT HC)]]. Qed.

Lemma drv_minv_qtight : forall S cap dl, drv_minv S cap dl -> qtight S.
Proof. intros S cap dl (_ & _ & _ & H & _). exact H. Qed.

Lemma drv_minv_fa_clean : forall S cap dl, drv_minv S cap dl -> fa_clean S.
Proof. intros S cap dl (_ & _ & _ & _ & H). exact H. Qed.
Definition malloc_site_tfa : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(n : Z) (KB : TSet),
drv_pre ly S W regs mem md ->
getr regs 10%bv = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In [pc_malloc_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
AI tfibsegs (w_H W) (w_A W) md ->
(forall ly' S' W' regs' mem' md' trc tr (p : sptr),
p <> PNull -> In trc (as_universe B) -> apath (malloc n trc S) tr (p, S') ->
acall_post tfibsegs B ASTACK ly S W regs mem md
(fun a => sptr_addr B ly' p <= a < sptr_addr B ly' p + req_size n) ly' S' W' regs' mem' md' ->
getr regs' 10%bv = w64 (sptr_addr B ly' p) -> wle W W' -> AI tfibsegs (w_H W') (w_A W') md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') KB) ->
srealizes tfibsegs (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md) KB.
Definition rd0_file_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate)
(a0 p data : list byte) (pb : sptr) (rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
valid_fs (in_fs inp) ->
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) [a0; p] (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] -> pb <> PNull ->
sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) A_BUF) -> st_nev S <= 1 ->
prim_pristine_except S [] -> quar_bytes S = 0 -> frames S = [] -> qtight S ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) -> m_channel_reader md = true ->
(* Theorem Labs, 2026-11: the meter's free-array invariant, and files shorter than the header only. *)
fa_clean S -> dlen data < HDR_MIN ->
srealizes tfibsegs (mkCfg ms md) (RPX data (in_fs inp) READ_FUEL CAP0).
Definition rd0_dir_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate)
(a0 p : list byte) (pb : sptr) (rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
p = dot_path ->
st_ok tfibsegs (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) [a0; p] (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] ->
sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) A_BUF) -> st_nev S <= 1 ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir -> m_channel_reader md = true ->
srealizes tfibsegs (mkCfg ms md) (diag (msg_read_error p) (in_fs inp)).

Definition drv_epre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd)   /\ YK0s.ret_ok (getr regs 1%bv) /\
spZ regs mod 16 = 0 /\ sp_window_lo - 2304 <= spZ regs <= sp_window_hi /\ ly_top ly - 6239 <= spZ regs <= ly_top ly + 48 /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B).

Definition memcpy_site_tfa : Prop :=
forall ly S W regs mem md d x n,
drv_epre ly S W regs mem md ->
getr regs 10%bv = w64 d -> getr regs 11%bv = w64 x -> getr regs 12%bv = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok tfibsegs W regs mem x n -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
SRr tfibsegs W (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10%bv = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

Definition chk_regs_post (regs regs' : bvmap 5 word) : Prop :=
forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 20 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).

Definition read_check_tfa : Prop :=
forall ly S W regs mem md (n ptr : Z),
drv_epre ly S W regs mem md ->
getr regs 10%bv = w64 n -> getr regs 9%bv = w64 ptr -> 0 < n < 2 ^ 31 -> 0 <= ptr -> ptr + n <= 2 ^ 63 ->
amem_range ptr n -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF ptr n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) ptr n ->
SRr tfibsegs W (cfg_at tfibsegs A_CHK regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs A_CHK_END regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ chk_regs_post regs regs' /\ same_but_materialized md md' /\
getr regs' 10%bv = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition free_site_tfa : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p : sptr) (n : Z),
drv_pre ly S W regs mem md ->
In (p, n) (blocks S) -> getr regs 10%bv = w64 (sptr_addr B ly p) ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
SRr tfibsegs W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free p trc S) tr (tt, S') /\
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B ASTACK ly S W regs mem md
(fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' S' W' regs' mem' md').

Definition rderr_leaf_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (p : list byte) (zp : Z) (fs : Fs),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 0xa0968 -> getr regs 11%bv = w64 0x1d8a1 -> getr regs 12%bv = w64 zp ->
getr regs 1%bv = w64 0x804d0 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
usp <= zp -> zp + Z.of_nat (length p) + 1 < kHighMemEnd -> ~ In NUL p -> Z.of_nat (length p) <= 131071 ->
YP03.bytes_at (mrestrict (w_H W) mem) zp (p ++ [NUL]) ->
(forall a, zp + Z.of_nat (length p) < a < zp + Z.of_nat (length p) - (zp + Z.of_nat (length p)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_channel_reader md = true -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 0x421c8) mem (seg_rom tfibsegs)) md) (diag (msg_read_error p) fs).

Definition refused_leaf_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 0xa0968 -> getr regs 11%bv = w64 0x19804 -> getr regs 12%bv = w64 67108864 ->
getr regs 1%bv = w64 0x804d0 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_channel_reader md = true -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 0x421c8) mem (seg_rom tfibsegs)) md) (diag msg_refused fs).

Definition hdr_tfa : Prop :=
forall (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate)
(a0 p data : list byte) (pb : sptr) (cap : Z) (rnd : EntryDraw),
valid_sp sp -> in_argv inp = [a0; p] ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> dlen data < cap ->
st_ok tfibsegs (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) S_HDR (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) [a0; p] (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, cap)] ->
sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) A_BUF) ->
bv_unsigned (ew (havoc (ELV sp rnd a0 p inp xw xd) K_M1 ws) A_LEN) = dlen data ->
65536 <= cap <= 2 ^ 26 -> st_nev S <= 64 ->
drv_minv S cap (dlen data) ->
YP03.bytes_at (mrestrict (w_H W) (ms_mem ms)) (sptr_addr B ly pb) data ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> m_channel_reader md = true ->
(* Theorem Labs, 2026-11: files shorter than the header only: the short leaf, not the harness. *)
dlen data < HDR_MIN ->
srealizes tfibsegs (mkCfg ms md) (POSTX data (in_fs inp)).
End b.
