(* copied from cgif_file lib/A/AD1v.v by rules r1,r2,r3,r4,r6,r8,r9,rC, generator ed5c0821ce98f1d99fcd7466c0aa65f7671a8daf838ab8f2b2da9f5038f22ee4 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1v.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (8 numerals; per-numeral report). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD1ucf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00cf YG01cf YG0dcf YG0ncf YGcfNames YGcfPristine.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre YGcfPath.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfPres.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* KF-COUNT #7: the driver's allocator calls before the loop's first call, once the input buffer holds cap bytes,
   are at most ns_pre cap mallocs: the input buffer's malloc(65536) (A/AD26cf.v m1_common) and one malloc(2 * cap)
   per doubling of the buffer from 2 ^ 16 (A/AD23cf.v gr_grow; its free of the old buffer adds none to the count).
   So ns_pre 65536 = 1 and ns_pre cap <= 11 for cap <= 2 ^ 26. *)
Definition ns_pre (cap : Z) : Z := Z.log2 cap - 15.
Lemma ns_pre_cap0 : ns_pre 65536 = 1. Proof. reflexivity. Qed.
Lemma ns_pre_double : forall cap, 0 < cap -> ns_pre (2 * cap) = ns_pre cap + 1.
Proof. intros cap H. unfold ns_pre. rewrite Z.log2_double by lia. lia. Qed.
Lemma ns_pre_max : forall cap, 0 < cap <= 2 ^ 26 -> ns_pre cap <= 11.
Proof.
intros cap H. unfold ns_pre. pose proof (Z.log2_le_mono cap (2 ^ 26) ltac:(lia)) as X.
rewrite Z.log2_pow2 in X by lia. lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Variable B : asyms.
(* the cf allocator's non-primary room between the driver's allocator calls (A/AD1w_cf.v's NP): it replaces the
   donor's event bounds `st_nev S <= 1` / `st_nev S <= 64` at the driver's cut points; each allocator call takes
   ROOM_cf from it by iface_room_np_tail and gives it back by iface_room_np_step *)
Variable NP : astate -> Prop.
(* route R (RULE-SHAPES.md sec 0): the world relation of a step whose callee can re-hide shadow (the free sites
   below; the library call, A/AD1mcf.v). The cf instance takes R := wle' tfibsegs RZ_cf (A/AD1icf.v tfib_free_site).
   The three laws in the route-R crew's order and names. *)
Variable R : world tfibsegs -> world tfibsegs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle tfibsegs W W' -> R W W'.
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
(* W8's readable-stack conjunct at the call (A/AD1w_cf.v fr_lib_pre_drv: every byte of [spZ regs, ly_top ly) reads
   through the view), the part ABOVE the entry sp: the entry image (argv, envp, auxv, the strings) up to the stack top.
   Below the entry sp the driver's own windows give presence at every cut point. The driver writes nothing at or above
   the entry sp and every callee's journal keeps those bytes, so it is carried from main's hand-off to every call. *)
Definition stk_up (usp : Z) (ly : alayout) (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  forall a, usp <= a < ly_top ly -> aview tfibsegs (w_H W) mem a <> None.
Lemma stk_up_high : forall usp ly ly' (W W' : world tfibsegs) (m m' : word -> option byte),
  (forall a, usp <= a < 2 ^ 64 -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  ly_top ly' = ly_top ly -> usp <= sp_window_hi -> top_ok usp ly -> stk_up usp ly W m -> stk_up usp ly' W' m'.
Proof.
intros usp ly ly' W W' m m' HE Ht Hhi (T1 & _) HU a Ha. rewrite Ht in Ha.
rewrite HE by (unfold sp_window_hi in Hhi; lia). exact (HU a Ha).
Qed.
Lemma stk_up_lyle : forall usp n ly ly' (W : world tfibsegs) m, layout_le n ly ly' -> stk_up usp ly W m -> stk_up usp ly' W m.
Proof. intros usp n ly ly' W m (_ & _ & _ & _ & _ & _ & _ & _ & Et & _) HU a Ha. rewrite Et in Ha. exact (HU a Ha). Qed.
Lemma finv_run : forall ly S Hp_cf (W : world tfibsegs) mem0 md (H : word -> bool) E rs (m m' : word -> option byte) usp,
ARcf tfibsegs B ly S Hp_cf W mem0 md -> frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb AD1ycf.drv_win_ok rs = true ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp -> usp <= sp_window_hi -> top_ok usp ly -> FINV ly H m -> FINV ly H m'.
Proof.
intros ly S Hp_cf W mem0 md H E rs m m' usp HAR HF Hok E0 Ulo Uhi (_ & Hlo & Hhi & HCT) HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_stretch B ly S _ W mem0 md H E rs m m' usp HAR HF Hok E0); [| | exact Ulo | exact HFI].
- rewrite Hlo. unfold ASAN_CEIL, stack_max_size in *. lia.
- rewrite Hhi. unfold kHighMemEnd, sp_window_hi in *. lia.
Qed.
Lemma finv_site : forall (HB : TfibSyms B) (ARL : AR_laws_cf tfibsegs B) stk ly S Hp_cf (W : world tfibsegs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp,
ARcf tfibsegs B ly S Hp_cf W mem md -> YGcfRehidePost.acall_post_cf_rh tfibsegs B stk ly S Hp_cf W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n)) ->
top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
FINV ly (w_H W) mem -> FINV ly' (w_H W') mem'.
Proof.
intros HB ARL stk ly S Hp_cf W regs mem md E ly' S' W' regs' mem' md' usp HAR HP HE (_ & Hlo & Hhi & HCT) Ulo Uhi Hsp Hstk HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_acall_post B HB ARL stk ly S _ W regs mem md E ly' S' W' regs' mem' md' HAR HP HE); [| | | exact HFI].
- rewrite Hlo. unfold ASAN_CEIL, stack_max_size in *. lia.
- rewrite Hhi. unfold kHighMemEnd, sp_window_hi in *. lia.
- unfold sp_window_lo in *. lia.
Qed.
Lemma finv_icpt : forall (HB : TfibSyms B) (ARL : AR_laws_cf tfibsegs B) ly S Hp_cf (W : world tfibsegs) mem md (mem' : word -> option byte) (P : Z -> Prop) lo hi usp,
ARcf tfibsegs B ly S Hp_cf W mem md -> top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
usp - 65536 <= lo -> hi <= usp ->
(forall a, P a -> exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
FINV ly (w_H W) mem -> FINV ly (w_H W) mem'.
Proof.
intros HB ARL ly S Hp_cf W mem md mem' P lo hi usp HAR (_ & Hlo & Hhi & HCT) Ulo Uhi Hfr Hl Hh HP HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_off B ly S _ W mem md mem' P (fun a => lo <= a < hi) HAR Hfr); [|exact HFI].
intros a Ha. split.
- intros HPa. destruct (HP a HPa) as (p0 & n0 & Hin & Hpa). exact (finv_avoids_block B ARL ly S _ W mem md p0 n0 a HAR Hin Ha Hpa).
- apply (finv_avoids_stack B ly S _ W mem md lo hi a HAR); [| | | exact Ha].
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
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W mem md ->
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
stk_up (bv_unsigned sp) ly W (ms_mem ms) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
(* field round 3 (Part A): the hand-off memory's RELRO bytes, carried from main's entry *)
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_loaded data (in_fs inp)).
Definition dir_arm_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p : list byte),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) -> p = dot_path ->
st_ok tfibsegs (ELV sp a0 p inp xw xd) ss_m1 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_dir p (in_fs inp)).
Definition drv_pre (ly : alayout) (S : astate) (Hp_cf : list Z) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARcf tfibsegs B ly S Hp_cf W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd) /\ (Hp_cf = [] /\ ROOM_cf S) /\
YK0s.ret_ok (getr regs 1%bv) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ ly_top ly - 4128 <= spZ regs <= ly_top ly + 32 /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
s0Z regs < alloc_ceiling /\
(* field round 3: acall_pre_cf's hull admission at the call state (Reusable/YG0dcf.v acall_pre_cf); each site that
   builds drv_pre proves it from the run count's bound (A/AD1pcf.v HULL_NS), or at init_state by cf_hull_ok_init.
   Part A: and its read-only bytes at the call memory (part 3c: arodata_ok_cf over aro_addr_cf, the RELRO range and
   the cf_ro_reads ranges), carried from main's hand-off (relro_ok below) *)
qtight S /\ cf_hull_ok S /\ arodata_ok_cf tfibsegs B mem.
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
apath (malloc_cf (2 * cap) trc S) tr (p, S1) ->
Wf_cf U S1 -> In (pb, cap) (blocks S1) -> apath (free_cf pb trc' S1) tr' (tt, S2) ->
frames S1 = frames S -> frames S2 = frames S1 ->
(qtight S -> qtight S1) -> (qtight S1 -> qtight S2) ->
drv_minv S2 (2 * cap) dl.
Proof.
intros U S S1 S2 cap dl trc tr p trc' tr' pb (Hcs & Hq & Hfr & Hqt) Hcap Hdl HM HW Hin HF HF1 HF2 HQ1 HQ2.
assert (X : exists cs, prim_pristine_except S cs /\ forall c, In c cs -> In c [kBatchClass]).
{ destruct Hcs as [[_ HP] | [_ HP]]; eexists; (split; [exact HP|]); [intros c [] | intros c Hc; exact Hc]. }
destruct X as (cs & HP & Hsub).
destruct (malloc_cf_sec_keeps_pristine (2 * cap) trc S tr p S1 cs (from_primary_big (2 * cap) ltac:(lia)) HM HP) as [HP1 HQ1'].
assert (Hreq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
destruct (pristine_free_norecycle_cf U pb cap trc' S1 tr' S2 cs HW Hin
ltac:(rewrite Hreq, HQ1'; unfold kBatchBytes, kQuarantineMax; lia) HF HP1) as [HP2 HQ2'].
split; [| split; [| split]].
- right. split; [lia|]. apply (prim_pristine_mono S2 (kBatchClass :: cs)); [|exact HP2].
intros c [<-|Hc]; [left; reflexivity | exact (Hsub c Hc)].
- rewrite Hreq, HQ1' in HQ2'. unfold kBatchBytes in HQ2'. lia.
- rewrite HF2, HF1. exact Hfr.
- exact (HQ2 (HQ1 Hqt)).
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
forall (ly : alayout) (S : astate) (Hp_cf : list Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(n : Z) (KB : TSet),
drv_pre ly S Hp_cf W regs mem md ->
getr regs 10%bv = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
(* a granted malloc_cf returns a block only with room in its class (YGcfPath.malloc_cf_success_of_room); the donor
   excluded the null return by cgif's ns flag *)
room_cf n S ->
In [pc_malloc_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
AI tfibsegs (w_H W) (w_A W) md ->
(forall ly' S' W' regs' mem' md' trc tr (p : sptr),
p <> PNull -> In trc (as_universe B) -> apath (malloc_cf n trc S) tr (p, S') ->
acall_post_cf tfibsegs B ASTACK ly S Hp_cf W regs mem md
(* malloc_leaf_cf's frame (YG0dcf.v:293-294): the new block, and the error-message buffer before and after *)
(fun a => (sptr_addr B ly' p <= a < sptr_addr B ly' p + req_size n) \/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' S'))
ly' S' W' regs' mem' md' ->
xs_placed_cf ly' S' ->
getr regs' 10%bv = w64 (sptr_addr B ly' p) -> wle W W' -> AI tfibsegs (w_H W') (w_A W') md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') KB) ->
srealizes tfibsegs (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md) KB.
(* KF-COUNT #7: the run count (A/AD1mcf.v NS; at MT_sec, a Theorem Labs lane's nsec_cf), carried from the start state init_state to
   the loop's first call: at rd0_file_tfa and hdr_tfa it is at most NS init_state plus the mallocs so far (ns_pre).
   Declared after the section's lemmas, so that none of them takes it. *)
Variable NS : astate -> Z.
Definition rd0_file_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (Hp_cf : list Z) (a0 p data : list byte) (pb : sptr),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
NS S <= NS init_state + 1 ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
stk_up (bv_unsigned sp) ly W (ms_mem ms) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S Hp_cf W (ms_mem ms) md -> Hp_cf = [] -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] -> pb <> PNull -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) -> NP S -> xs_placed_cf ly S ->
prim_pristine_except S [] -> quar_bytes S = 0 -> frames S = [] -> qtight S ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (RPX data (in_fs inp) READ_FUEL CAP0).
Definition rd0_dir_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (Hp_cf : list Z) (a0 p : list byte) (pb : sptr),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) -> p = dot_path ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S Hp_cf W (ms_mem ms) md -> Hp_cf = [] -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) -> NP S ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
srealizes tfibsegs (mkCfg ms md) (diag (msg_read_error p) (in_fs inp)).
Definition drv_epre (ly : alayout) (S : astate) (Hp_cf : list Z) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARcf tfibsegs B ly S Hp_cf W mem md /\ (ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd)   /\ YK0s.ret_ok (getr regs 1%bv) /\
spZ regs mod 16 = 0 /\ sp_window_lo - 2304 <= spZ regs <= sp_window_hi /\ ly_top ly - 6239 <= spZ regs <= ly_top ly + 48 /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B).
Definition memcpy_site_tfa : Prop :=
forall ly S Hp_cf W regs mem md d x n,
drv_epre ly S Hp_cf W regs mem md ->
getr regs 10%bv = w64 d -> getr regs 11%bv = w64 x -> getr regs 12%bv = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok tfibsegs W regs mem x n -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
SRr tfibsegs W (cfg_at tfibsegs (pc_wrap_memcpy (as_code B)) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARcf tfibsegs B ly S Hp_cf W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10%bv = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition chk_regs_post (regs regs' : bvmap 5 word) : Prop :=
forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 20 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition read_check_tfa : Prop :=
forall ly S Hp_cf W regs mem md (n ptr : Z),
drv_epre ly S Hp_cf W regs mem md ->
getr regs 10%bv = w64 n -> getr regs 9%bv = w64 ptr -> 0 < n < 2 ^ 31 -> 0 <= ptr -> ptr + n <= 2 ^ 63 ->
amem_range ptr n -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF ptr n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) ptr n ->
SRr tfibsegs W (cfg_at tfibsegs A_CHK regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs A_CHK_END regs' mem' md' /\
ARcf tfibsegs B ly S Hp_cf W mem' md' /\ chk_regs_post regs regs' /\ same_but_materialized md md' /\
getr regs' 10%bv = w64 n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* ROW T (route R): the free call can re-hide shadow (the secondary recycle's madvise), so the site's step relation is
   SRrG at R (at the cf instance R := wle' over the fixed zone RZ_cf: the hidden set grows only inside it) and its post
   is the primed YGcfRehidePost.acall_post_cf_rh (the world grows only inside dead_shadow_new, the view frame holds
   off it); the site is AD1icf.tfib_free_site, from the primed contract YG0dcfR.afree_realizes_cf_rh *)
Definition free_site_tfa : Prop :=
forall (ly : alayout) (S : astate) (Hp_cf : list Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p : sptr) (n : Z),
drv_pre ly S Hp_cf W regs mem md ->
In (p, n) (blocks S) -> getr regs 10%bv = w64 (sptr_addr B ly p) ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
SRrG tfibsegs R W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free_cf p trc S) tr (tt, S') /\
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly S Hp_cf W regs mem md
(fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' S' W' regs' mem' md').
Definition rderr_leaf_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (Hp_cf : list Z) (usp : Z) (p : list byte) (zp : Z) (fs : Fs),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 0xa2028 -> getr regs 11%bv = w64 0x1d744 -> getr regs 12%bv = w64 zp ->
getr regs 1%bv = w64 0x820b0 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
usp <= zp -> zp + Z.of_nat (length p) + 1 < kHighMemEnd -> ~ In NUL p -> Z.of_nat (length p) <= 131071 ->
YP03.bytes_at (mrestrict (w_H W) mem) zp (p ++ [NUL]) ->
(forall a, zp + Z.of_nat (length p) < a < zp + Z.of_nat (length p) - (zp + Z.of_nat (length p)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S Hp_cf W mem md -> top_ok usp ly ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 0x421d8) mem (seg_rom tfibsegs)) md) (diag (msg_read_error p) fs).
Definition refused_leaf_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (Hp_cf : list Z) (usp : Z) (fs : Fs),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 0xa2028 -> getr regs 11%bv = w64 0x196f6 -> getr regs 12%bv = w64 67108864 ->
getr regs 1%bv = w64 0x820b0 -> spZ regs = usp - 128 -> getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_REGIONS ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S Hp_cf W mem md -> top_ok usp ly ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 0x421d8) mem (seg_rom tfibsegs)) md) (diag msg_refused fs).
Definition hdr_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (Hp_cf : list Z) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> dlen data < cap ->
NS S <= NS init_state + ns_pre cap ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) S_HDR (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
stk_up (bv_unsigned sp) ly W (ms_mem ms) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S Hp_cf W (ms_mem ms) md -> Hp_cf = [] -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) ->
bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_LEN) = dlen data -> 65536 <= cap <= 2 ^ 26 -> NP S -> xs_placed_cf ly S ->
drv_minv S cap (dlen data) ->
YP03.bytes_at (mrestrict (w_H W) (ms_mem ms)) (sptr_addr B ly pb) data ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
arodata_ok_cf tfibsegs B (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (POSTX data (in_fs inp)).
End b.
(* the RELRO keep lemmas live in their own section, over B alone (Section b's NP / R are not theirs) *)
Section aro. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.
Variable B : asyms.
(* ---- field round 3 (Part A; part 3c): the call memory's read-only bytes, arodata_ok_cf (Reusable/YG0dcf.v) over
   aro_addr_cf (the RELRO range [cf_relro_lo, cf_relro_hi) or a range of cf_ro_reads), carried beside FINV from main's
   hand-off to every allocator call. The image fact relro_ok: the RELRO range and each cf_ro_reads range lie in one
   segment of the image (YG0ncf.relro_seg_t; image A: ReplyRelroGeoA.relro_seg_reply_A) and below the driver's image
   windows (AD1ycf.DRVW_lo's 0xa1f78; image A: cf_relro_hi = 0x9f000, the read ranges end by 0x20c00, one vm_compute
   at the instance). Such a byte is then an image byte, visible in every world (YGcfPres.cfp_img_unhidden), no block
   or stack byte, and below every absolute write window (the driver's DRVW, the stdio FILEs). So each step keeps the
   fact: the driver's code by its frame (aro_run), an allocator call by its post's view frame (aro_site), an
   interceptor by its view frame (aro_icpt, aro_high2). ---- *)
Definition relro_ok : Prop := relro_seg_t tfibsegs /\ cf_relro_hi <= 0xa1f78 /\
  forallb (fun r => fst r + snd r <=? 0xa1f78) cf_ro_reads = true.
(* an aro_addr_cf byte is an image byte, in 64 bits, below the driver's image windows *)
Lemma aro_img : forall a, relro_ok -> aro_addr_cf a -> 0 <= a < 2 ^ 64 /\ in_img tfibsegs a /\ a < 0xa1f78.
Proof.
intros a ((RS & RD) & HI & HR) [Ha|Ha].
- destruct RS as (sg & Hsg & L1 & L2). pose proof (N2Z.is_nonneg (seg_base sg)).
  split; [lia|]. split; [exists sg; split; [exact Hsg | lia] | lia].
- apply Exists_exists in Ha as ([s n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  rewrite forallb_forall in HR. specialize (HR _ Hin). apply Z.leb_le in HR. cbn [fst snd] in HR.
  rewrite Forall_forall in RD. destruct (RD _ Hin) as (sg & Hsg & L1 & L2). cbn [fst snd] in L1, L2.
  pose proof (N2Z.is_nonneg (seg_base sg)).
  split; [lia|]. split; [exists sg; split; [exact Hsg | lia] | lia].
Qed.
Lemma aview_unhidden : forall (H : word -> bool) (mem : word -> option byte) a, H (Z_to_bv 64 a) = false ->
  aview tfibsegs H mem a = option_map (fun b : byte => bv_unsigned b)
    (match mem (Z_to_bv 64 a) with Some b => Some b | None => seg_rom tfibsegs (Z_to_bv 64 a) end).
Proof. intros H mem a U. unfold aview, mbyte, mrestrict. rewrite U. reflexivity. Qed.
(* the core keep: the views agree at every non-owned aro_addr_cf byte *)
Lemma aro_view : forall (W W' : world tfibsegs) (mem mem' : word -> option byte), relro_ok ->
  (forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
     aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  arodata_ok_cf tfibsegs B mem -> arodata_ok_cf tfibsegs B mem'.
Proof.
intros W W' mem mem' RO HV AR a b E Ha NO.
destruct (aro_img a RO Ha) as (Hb & Hi & _).
pose proof (HV a Ha NO) as X.
rewrite (aview_unhidden _ mem' a (YGcfPres.cfp_img_unhidden tfibsegs W' a Hb Hi)),
  (aview_unhidden _ mem a (YGcfPres.cfp_img_unhidden tfibsegs W a Hb Hi)), E in X. cbn [option_map] in X.
destruct (mem (Z_to_bv 64 a)) as [b0|] eqn:E0; try rewrite E0 in X; cbn [option_map] in X.
- rewrite (AR a b0 E0 Ha NO). injection X as X. f_equal. apply bv_eq. symmetry. exact X.
- destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [r|] eqn:Er; try rewrite Er in X; cbn [option_map] in X; [|discriminate X].
  injection X as X. f_equal. apply bv_eq. symmetry. exact X.
Qed.
(* the driver's own code: its frame covers stack windows and the DRVW windows only *)
Lemma aro_run : forall (W : world tfibsegs) E rs (m m' : word -> option byte), relro_ok ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forallb AD1ycf.drv_win_ok rs = true ->
  sp_window_lo <= bv_unsigned (ew E 0) -> arodata_ok_cf tfibsegs B m -> arodata_ok_cf tfibsegs B m'.
Proof.
intros W E rs m m' RO HF Hok Hsp. apply (aro_view W W m m' RO).
intros a Ha NO. destruct (aro_img a RO Ha) as (Hb & _ & HI). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite YK00.u64_lit by lia. intros Hw.
destruct (AD1ycf.in_wrange_drv E rs a Hok Hw) as [Hs|Hd].
- unfold sp_window_lo in Hsp. lia.
- apply AD1ycf.DRVW_lo in Hd. lia.
Qed.
(* errno lies above every aro_addr_cf range (round 3's errno_relro_t, from the windows' floor) *)
Lemma aro_errno : forall (HB : TfibSyms B), relro_ok -> errno_relro_t B.
Proof.
intros HB ((_ & _) & HI & HR). unfold errno_relro_t. rewrite (ts_errno B HB). unfold TFIB_ERRNO.
split; [right; lia|]. rewrite forallb_forall in HR. apply Forall_forall. intros r Hr.
specialize (HR r Hr). apply Z.leb_le in HR. right. lia.
Qed.
(* an allocator call: the post's view frame. Its exception set E (the call's block, the error-message buffer's
   extents) lies off the image, the aro_addr_cf ranges on it *)
Lemma aro_site : forall (HB : TfibSyms B) stk ly S Hp_cf (W : world tfibsegs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp,
relro_ok ->
ARcf tfibsegs B ly S Hp_cf W mem md -> YGcfRehidePost.acall_post_cf_rh tfibsegs B stk ly S Hp_cf W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> ~ in_img tfibsegs a) ->
top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
arodata_ok_cf tfibsegs B mem -> arodata_ok_cf tfibsegs B mem'.
Proof.
intros HB stk ly S Hp_cf W regs mem md E ly' S' W' regs' mem' md' usp RO HAR HP HE (_ & Hlo & Hhi & HCT) Ulo Uhi Hsp Hstk.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
rewrite YGcfRehidePost.acall_post_cf_rh_unfold in HP. destruct HP as (HAR' & _ & _ & _ & _ & HV & _).
apply (aro_view W W' mem mem' RO). intros a Ha NO.
destruct (aro_img a RO Ha) as (Hb & Hi & HI).
destruct (relro_apart_cf tfibsegs B ly S Hp_cf W mem md a HAR (proj1 RO) Ha NO) as (RI & _ & NA & _).
destruct (relro_apart_cf tfibsegs B ly' S' Hp_cf W' mem' md' a HAR' (proj1 RO) Ha NO) as (_ & _ & NA' & _).
apply HV; [exact Hb | exact NA | exact NA' | | |].
- apply (relro_not_scratch_cf B ly stk regs a); [exact (amc_layout _ _ _ _ _ (proj1 HAR)) | | | exact Ha | exact RI].
  + rewrite Hlo. unfold ASAN_CEIL, stack_max_size, sp_window_lo in *. lia.
  + exact (aro_errno HB RO).
- intros HEa. exact (HE a HEa Hi).
- intros HD. pose proof (YGcfRehidePost.dead_shadow_new_not_low ly S S' a HD) as X. unfold kLowMemEnd in X. lia.
Qed.
Lemma aro_site_x : forall (HB : TfibSyms B) stk ly S Hp_cf (W : world tfibsegs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp,
relro_ok ->
ARcf tfibsegs B ly S Hp_cf W mem md -> acall_post_cf tfibsegs B stk ly S Hp_cf W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> ~ in_img tfibsegs a) ->
top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
arodata_ok_cf tfibsegs B mem -> arodata_ok_cf tfibsegs B mem'.
Proof.
intros HB stk ly S Hp_cf W regs mem md E ly' S' W' regs' mem' md' usp RO HAR HP.
exact (aro_site HB stk ly S Hp_cf W regs mem md E ly' S' W' regs' mem' md' usp RO HAR
  (YGcfRehidePost.acall_post_cf_rh_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP)).
Qed.
(* an interceptor: its view frame off a stack window and off live blocks (finv_icpt's premises) *)
Lemma aro_icpt : forall (ARL : AR_laws_cf tfibsegs B) ly S Hp_cf (W : world tfibsegs) mem md (mem' : word -> option byte) (P : Z -> Prop) lo hi usp,
relro_ok -> ARcf tfibsegs B ly S Hp_cf W mem md -> sp_window_lo <= usp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
usp - 65536 <= lo ->
(forall a, P a -> exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
arodata_ok_cf tfibsegs B mem -> arodata_ok_cf tfibsegs B mem'.
Proof.
intros ARL ly S Hp_cf W mem md mem' P lo hi usp RO HAR Ulo Hfr Hl HP.
apply (aro_view W W mem mem' RO). intros a Ha NO. destruct (aro_img a RO Ha) as (Hb & Hi & HI).
apply Hfr; [exact Hb | |].
- intros HPa. destruct (HP a HPa) as (p0 & n0 & Hin & Hpa).
  exact (proj2 (alc_client_img _ _ ARL ly S _ W mem md a HAR (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hin Hpa))))) Hi).
- unfold sp_window_lo in Ulo. lia.
Qed.
(* a step whose view frame excepts two sets, both above the driver's image windows' start (a stack window, a stdio
   FILE or its buffer) *)
Lemma aro_high2 : forall (W : world tfibsegs) (mem mem' : word -> option byte) (X Y : Z -> Prop), relro_ok ->
  (forall a, X a -> 0xa1f78 <= a) -> (forall a, Y a -> 0xa1f78 <= a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> ~ Y a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  arodata_ok_cf tfibsegs B mem -> arodata_ok_cf tfibsegs B mem'.
Proof.
intros W mem mem' X Y RO HX HY Hfr. apply (aro_view W W mem mem' RO). intros a Ha NO.
destruct (aro_img a RO Ha) as (Hb & _ & HI).
apply Hfr; [exact Hb | intros Hx; pose proof (HX a Hx) | intros Hy; pose proof (HY a Hy)]; lia.
Qed.
End aro.
