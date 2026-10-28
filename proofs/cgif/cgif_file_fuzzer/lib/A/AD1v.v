(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YD2n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
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
AR tfibsegs B ly S W mem0 md -> frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb AD1y.drv_win_ok rs = true ->
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
Lemma argv_str_fits : forall sp argv envp k, entry_stack_fits sp argv envp -> (k < length argv)%nat ->
z_argv (bv_unsigned sp) argv envp k + Z.of_nat (length (nth k argv [])) + 1 <= kHighMemEnd.
Proof.
intros sp argv envp k Hfit Hk. pose proof (YP08.z_argv_end sp argv envp k Hk) as Z1.
unfold entry_stack_fits, entry_stack_span, sp_window_hi in Hfit. rewrite !total_arg_bytes_Z in Hfit.
pose proof (YP08.struct_size_eq argv envp) as SE. unfold z_strs in Z1. unfold kHighMemEnd.
change (Z.of_nat StackLayout.auxv_size) with 160 in Hfit. pose proof (total_arg_bytes_nonneg envp). rewrite total_arg_bytes_Z in *. lia.
Qed.
Lemma argv_str_fits' : forall sp argv envp k, entry_stack_fits sp argv envp -> (k < length argv)%nat ->
z_argv (bv_unsigned sp) argv envp k + Z.of_nat (length (nth k argv [])) + 1 < kHighMemEnd.
Proof.
intros sp argv envp k Hfit Hk. pose proof (YP08.z_argv_end sp argv envp k Hk) as Z1.
unfold entry_stack_fits, entry_stack_span, sp_window_hi in Hfit. rewrite !total_arg_bytes_Z in Hfit.
pose proof (YP08.struct_size_eq argv envp) as SE. unfold z_strs in Z1. unfold kHighMemEnd.
change (Z.of_nat StackLayout.auxv_size) with 160 in Hfit. pose proof (total_arg_bytes_nonneg envp). rewrite total_arg_bytes_Z in *. lia.
Qed.
Lemma argv_over_read : forall sp (rdraw : EntryDraw) argv envp (two : bool) (m : word -> option byte) k,
valid_sp sp -> (k < length argv)%nat -> runs_at (bv_unsigned sp) m (runs_main_tfa two sp argv envp) ->
forall a, z_argv (bv_unsigned sp) argv envp k + Z.of_nat (length (nth k argv [])) < a
< z_argv (bv_unsigned sp) argv envp k + Z.of_nat (length (nth k argv []))
- (z_argv (bv_unsigned sp) argv envp k + Z.of_nat (length (nth k argv []))) mod 8 + 8 ->
m (Z_to_bv 64 a) <> None.
Proof.
intros sp rdraw argv envp two m k Hsp Hk HR a Ha.
assert (HB : YP03.bytes_at m (z_strs (bv_unsigned sp) argv envp) (stack_strs argv envp)).
{ apply (runs_at_nth _ _ _ (if two then 3 else 2)%nat _ _ HR). destruct two; reflexivity. }
set (q := z_argv (bv_unsigned sp) argv envp k + Z.of_nat (length (nth k argv []))) in *.
assert (Hlen : z_strs (bv_unsigned sp) argv envp + Z.of_nat (length (stack_strs argv envp)) = z_rand (bv_unsigned sp) argv envp).
{ pose proof (YP08.stack_tail_end sp argv envp rdraw) as BT. unfold stack_strs.
replace (stack_tail argv envp rdraw) with ((flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) (pad_len argv envp)) ++ YP08.rand_bytes rdraw) in BT
by (unfold stack_tail; rewrite !app_assoc; reflexivity).
rewrite length_app in BT. pose proof (YP08.length_rand_bytes rdraw) as LR. rewrite LR in BT. lia. }
pose proof (YP08.z_argv_end sp argv envp k Hk) as Z1.
pose proof (YP08.z_strs_rand sp argv envp) as Z2.
assert (Hlo : z_strs (bv_unsigned sp) argv envp <= q) by (unfold q, z_argv; lia).
assert (Hz8 : z_rand (bv_unsigned sp) argv envp mod 8 = 0).
{ unfold z_rand. rewrite <- Zplus_mod_idemp_r, (YP08.rand_off_mod8 argv envp), Z.add_0_r.
pose proof (YP08.mod8_of_mod16 (bv_unsigned sp) 0 (proj2 (proj2 Hsp))) as Hm8. rewrite Z.add_0_r in Hm8. exact Hm8. }
pose proof (Z.div_mod q 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (z_rand (bv_unsigned sp) argv envp) 8 ltac:(lia)) as D3.
assert (Hal : q - q mod 8 + 8 <= z_rand (bv_unsigned sp) argv envp) by lia.
replace a with (z_strs (bv_unsigned sp) argv envp + Z.of_nat (Z.to_nat (a - z_strs (bv_unsigned sp) argv envp))) by lia.
rewrite (HB (Z.to_nat (a - z_strs (bv_unsigned sp) argv envp))) by lia.
destruct (nth_error _ _) eqn:Hn; [discriminate|]. apply nth_error_None in Hn. lia.
Qed.
Definition cannot_open_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ly : alayout) (a0 p : list byte) (e : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) ->
regs_ok (ELV sp a0 p inp xw xd) (ss_regs ss_open) regs ->
mem_ok tfibsegs (ELV sp a0 p inp xw xd) (mrestrict (w_H W) mem) (ss_mem ss_open) ->
facts_ok (ELV sp a0 p inp xw xd) (ss_facts ss_open) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) mem) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W mem md ->
top_ok (bv_unsigned sp) ly -> m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
0 < e < 4096 ->
srealizes tfibsegs
(mkCfg (mkst (regupd regs 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (ss_pc ss_open)) 4) mem (seg_rom tfibsegs)) md)
(diag (msg_cannot_open p) (in_fs inp)).
Definition file_arm_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p data : list byte),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs (ELV sp a0 p inp xw xd) ss_m1 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_loaded data (in_fs inp)).
Definition dir_arm_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p : list byte),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) -> p = dot_path ->
st_ok tfibsegs (ELV sp a0 p inp xw xd) ss_m1 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_dir p (in_fs inp)).
Definition drv_pre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd) /\ st_nev S < EV_MAX /\
YK0s.ret_ok (getr regs 1%bv) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ ly_top ly - 4128 <= spZ regs <= ly_top ly + 32 /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
s0Z regs < alloc_ceiling /\
qtight S                                    .
Definition drv_minv (S : astate) (cap dl : Z) : Prop :=
((cap = 65536 /\ prim_pristine_except S []) \/ (2 ^ 17 <= cap <= 2 * dl /\ prim_pristine_except S [kBatchClass]))
/\ quar_bytes S <= 2 * cap /\ frames S = []
/\ qtight S                                      .
Lemma prim_pristine_mono : forall S cs cs',
(forall c, In c cs -> In c cs') -> prim_pristine_except S cs -> prim_pristine_except S cs'.
Proof. intros S cs cs' Hsub HP c Hc Hn. apply (HP c Hc). intros Hin. exact (Hn (Hsub c Hin)). Qed.
Lemma drv_minv_init : forall S dl, prim_pristine_except S [] -> quar_bytes S = 0 -> frames S = [] -> qtight S -> drv_minv S 65536 dl.
Proof. intros S dl HP HQ HF HT. split; [left; split; [reflexivity | exact HP] |]. split; [rewrite HQ; lia | split; [exact HF | exact HT]]. Qed.
Lemma drv_minv_frames : forall S cap dl, drv_minv S cap dl -> frames S = [].
Proof. intros S cap dl (_ & _ & H & _). exact H. Qed.
Lemma drv_minv_qtight : forall S cap dl, drv_minv S cap dl -> qtight S.
Proof. intros S cap dl (_ & _ & _ & H). exact H. Qed.
Lemma from_primary_big : forall n, 65536 < n -> from_primary n = false.
Proof.
intros n Hn. unfold from_primary, needed_primary, rounded_size, round_up, kMaxSize.
apply Z.leb_gt. pose proof (rz_size_bounds n) as [? _].
assert (n <= (Z.max n 8 + 8 - 1) / 8 * 8).
{ pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
lia.
Qed.
Lemma drv_minv_grow : forall U S S1 S2 (cap dl : Z) trc tr (p : sptr) trc' tr' (pb : sptr),
drv_minv S cap dl -> 65536 <= cap < 2 ^ 26 -> cap <= dl ->
apath (malloc (2 * cap) trc S) tr (p, S1) ->
Wf U S1 -> In (pb, cap) (blocks S1) -> apath (free pb trc' S1) tr' (tt, S2) ->
frames S1 = frames S -> frames S2 = frames S1 ->
(qtight S -> qtight S1) -> (qtight S1 -> qtight S2) ->
drv_minv S2 (2 * cap) dl.
Proof.
intros U S S1 S2 cap dl trc tr p trc' tr' pb (Hcs & Hq & Hfr & Hqt) Hcap Hdl HM HW Hin HF HF1 HF2 HQ1 HQ2.
assert (X : exists cs, prim_pristine_except S cs /\ forall c, In c cs -> In c [kBatchClass]).
{ destruct Hcs as [[_ HP] | [_ HP]]; eexists; (split; [exact HP|]); [intros c [] | intros c Hc; exact Hc]. }
destruct X as (cs & HP & Hsub).
destruct (pristine_malloc_sec (2 * cap) trc S tr p S1 cs (from_primary_big (2 * cap) ltac:(lia)) HM HP) as [HP1 HQ1'].
assert (Hreq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
destruct (pristine_free_norecycle U pb cap trc' S1 tr' S2 cs HW Hin
ltac:(rewrite Hreq, HQ1'; unfold kBatchBytes, kQuarantineMax; lia) HF HP1) as [HP2 HQ2'].
split; [| split; [| split]].
- right. split; [lia|]. apply (prim_pristine_mono S2 (kBatchClass :: cs)); [|exact HP2].
intros c [<-|Hc]; [left; reflexivity | exact (Hsub c Hc)].
- rewrite Hreq, HQ1' in HQ2'. unfold kBatchBytes in HQ2'. lia.
- rewrite HF2, HF1. exact Hfr.
- exact (HQ2 (HQ1 Hqt)).
Qed.
Lemma drv_minv_refusal : forall U S (cap dl n : Z) trc,
Wf U S -> drv_minv S cap dl -> 0 <= n < 2 ^ 32 -> dl - 6 - 32768 < n -> refusal_offered (malloc n trc S).
Proof.
intros U S cap dl n trc HW (Hcs & _ & _) Hn Hdl.
destruct (from_primary n) eqn:Hp.
- assert (Hmax : n < kMaxAllowedMalloc - kPage) by (unfold kMaxAllowedMalloc, kPage; lia).
destruct Hcs as [[_ HP] | [Hc HP]].
+ apply (malloc_refusal_prim U n trc S [] HW HP ltac:(lia) Hmax Hp). intros [].
+ apply (malloc_refusal_prim U n trc S [kBatchClass] HW HP ltac:(lia) Hmax Hp).
intros [H|[]]. pose proof (primary_geometry n ltac:(lia) Hp) as (_ & Hsz & _).
rewrite <- H in Hsz. unfold req_size in Hsz. destruct (Z.eqb_spec n 0); [lia|].
change (class_size kBatchClass) with 8192 in Hsz. pose proof (rz_size_bounds n). lia.
- apply malloc_refusal_sec; [exact Hp | unfold kMaxAllowedMalloc, kPage; lia].
Qed.
Lemma drv_minv_shape : forall S (cap dl n : Z),
drv_minv S cap dl -> 0 <= n < 2 ^ 32 -> dl - 6 - 32768 < n -> malloc_shape_pre n S.
Proof.
intros S cap dl n (Hcs & _ & _) Hn Hdl Hp.
destruct Hcs as [[_ HP] | [Hc HP]].
- exists []. split; [exact HP | intros []].
- exists [kBatchClass]. split; [exact HP|].
intros [H|[]]. pose proof (primary_geometry n ltac:(lia) Hp) as (_ & Hsz & _).
rewrite <- H in Hsz. unfold req_size in Hsz. destruct (Z.eqb_spec n 0); [lia|].
change (class_size kBatchClass) with 8192 in Hsz. pose proof (rz_size_bounds n). lia.
Qed.
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
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] -> pb <> PNull -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) -> st_nev S <= 1 ->
prim_pristine_except S [] -> quar_bytes S = 0 -> frames S = [] -> qtight S ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
srealizes tfibsegs (mkCfg ms md) (RPX data (in_fs inp) READ_FUEL CAP0).
Definition rd0_dir_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p : list byte) (pb : sptr),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) -> p = dot_path ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) -> st_nev S <= 1 ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
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
getr regs 10%bv = w64 0xa2578 -> getr regs 11%bv = w64 0x1d73c -> getr regs 12%bv = w64 zp ->
getr regs 1%bv = w64 0x80254 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
usp <= zp -> zp + Z.of_nat (length p) + 1 < kHighMemEnd -> ~ In NUL p -> Z.of_nat (length p) <= 131071 ->
YP03.bytes_at (mrestrict (w_H W) mem) zp (p ++ [NUL]) ->
(forall a, zp + Z.of_nat (length p) < a < zp + Z.of_nat (length p) - (zp + Z.of_nat (length p)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 0x4192c) mem (seg_rom tfibsegs)) md) (diag (msg_read_error p) fs).
Definition refused_leaf_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 0xa2578 -> getr regs 11%bv = w64 0x196bf -> getr regs 12%bv = w64 67108864 ->
getr regs 1%bv = w64 0x80254 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 0x4192c) mem (seg_rom tfibsegs)) md) (diag msg_refused fs).
Definition hdr_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> dlen data < cap ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) S_HDR (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) ->
bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_LEN) = dlen data -> 65536 <= cap <= 2 ^ 26 -> st_nev S <= 64 ->
drv_minv S cap (dlen data) ->
YP03.bytes_at (mrestrict (w_H W) (ms_mem ms)) (sptr_addr B ly pb) data ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes tfibsegs (mkCfg ms md) (POSTX data (in_fs inp)).
End b.
