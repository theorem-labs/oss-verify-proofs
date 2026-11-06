(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK15 YK18 YQ0k YN02 YQ0j YQ0b YQ0i YQ09 YQ0a YQ04 YO3p YO3v YK05 YA0i YA0l YA0e YG00 YG0a YG01 YG0m YG0h YG10 YG0u YG0d YC04 YL02 YB0z YF90 YD15 YD14 YD0f YD0l YD0g YD13 YD11.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP01.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCcx.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0p YG0r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
#[local] Notation ELV sp a0 p inp xw xd := (YQ0a.E0 sp [a0; p] (in_envp inp) xw xd).
Definition tail_at (ss : sstate) (E : YQ0j.env) (sp : word) (inp : ProcInput) (a0 p data : list byte)
(W : world trasegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (pb : sptr) (cap : Z) : Prop :=
st_ok trasegs E ss (restrict (w_H W) ms) /\
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb /\ bv_unsigned (ew E A_LEN) = dlen data /\
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) /\
AI trasegs (w_H W) (w_A W) md /\ AR trasegs B ly S W (ms_mem ms) md /\ top_ok (bv_unsigned sp) ly /\
blocks S = [(pb, cap)] /\ dev S <= 64 /\ 65536 <= cap <= 2 ^ 26 /\ dlen data < cap /\
blk (w_H W) (ms_mem ms) (sptr_addr B ly pb) (dlen data) data /\
m_fs md = in_fs inp /\ m_fds md = APSG.fds_std /\ drv_minv S cap (dlen data).
Definition short_leaf_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world trasegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> dlen data <= 5 ->
tail_at S_SHORT (havoc (ELV sp a0 p inp xw xd) K_M1 ws) sp inp a0 p data W ms md ly S pb cap ->
srealizes trasegs (mkCfg ms md) (diag msg_short (in_fs inp)).
Definition overrun_leaf_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world trasegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 <= dlen data < 6 + config_len data ->
tail_at S_OVR (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes trasegs (mkCfg ms md) (diag msg_overrun (in_fs inp)).
Definition post_P_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world trasegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> rrfc_universe B (payload_len data) -> 6 + config_len data <= dlen data ->
tail_at S_P (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes trasegs (mkCfg ms md)
(if payload_len data =? 0 then RUNS data (in_fs inp)
else t_alt2 (ex (if count_mode data then 0 else 2) (in_fs inp)) (RUNS data (in_fs inp))).
Definition lib_pre (ly : alayout) (S : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
AR trasegs B ly S W mem md /\ YK0s.ret_ok (getr regs 1%bv) /\ raZ regs = RA_LLVMF /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ spZ regs + 32 <= ly_top ly <= spZ regs + 4128 /\
ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
(forall a, spZ regs - LLVMF_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
s0Z regs < alloc_ceiling /\
qtightB S                                    .
Definition lib_site_tfa : Prop :=
forall ly S (W : world trasegs) (regs : bvmap 5 word) mem md p n,
lib_pre ly S W regs mem md ->
getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> vev S + EV_LIB <= VEV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview trasegs (w_H W) mem) ->
SRr trasegs W (cfg_at trasegs A_LLVMF regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' k,
c' = cfg_at trasegs RA_LLVMF regs' mem' md' /\
ajournal trasegs B LLVMF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10%bv = w64 0 /\
exists leak, Permutation (ablocks B ly' S') (leak ++ ablocks B ly S) /\
(leak = [] \/ exists a m, leak = [(a, m)] /\ 0 <= m < 3 * 2 ^ 16)).
Definition free_null_site_tfa : Prop :=
forall (ly : alayout) (S : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
drv_pre B ly S W regs mem md -> getr regs 10%bv = w64 0 ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
SRr trasegs W (cfg_at trasegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free PNull trc S) tr (tt, S') /\
c' = cfg_at trasegs (raZ regs) regs' mem' md' /\
acall_post trasegs B ASTACK ly S W regs mem md (fun _ => False) ly' S' W' regs' mem' md').
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition STDOUT_MUT (a : Z) : Prop := (STDOUT_LO <= a < STDOUT_HI) \/ (SOBUF_LO <= a < SOBUF_HI).
Definition stdout_img (H : word -> bool) (m : word -> option byte) : Prop :=
forall a, STDOUT_LO <= a < STDOUT_HI -> aview trasegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom trasegs (Z_to_bv 64 a)).
Definition xst_frame_tfa : Prop :=
forall k (H H' : word -> bool) (m m' : word -> option byte),
xst k H m -> (forall a, STDOUT_MUT a -> aview trasegs H' m' a = aview trasegs H m a) -> xst k H' m'.
Definition A_icpt_vprintf : Z := 0x420f4.
Definition RA_EMIT : Z := 0x80fa0.
Definition A_FMT_D : Z := 0x14861.
Definition PF_STK : Z := 9216.
Definition printf_pre (ly : alayout) (S : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
AR trasegs B ly S W mem md /\ raZ regs = RA_EMIT /\
spZ regs mod 16 = 0 /\ sp_window_lo - 288 <= spZ regs /\ ly_top ly - 4208 <= spZ regs <= ly_top ly - 128 /\
spZ regs + 288 <= sp_window_hi /\ ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
arodata_ok B (aview trasegs (w_H W) mem) /\
(forall a, spZ regs - PF_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
getr regs 10%bv = w64 A_FMT_D /\ getr regs 11%bv = w64 (spZ regs + 24) /\
rdword (aview trasegs (w_H W) mem) (spZ regs + 24) = Some 0.
Definition printf_post (ly : alayout) (S : astate) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(k' : nat) (T : TSet) : Prop :=
forall regs' mem' md',
AR trasegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' -> getr regs' 10%bv = w64 2 ->
xst k' (w_H W) mem' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PF_STK <= a < spZ regs) -> ~ STDOUT_MUT a -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDOUT_MUT a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI trasegs (w_H W) (w_A W) md' ->
srealizes trasegs (cfg_at trasegs (raZ regs) regs' mem' md') T.
Definition printf_first_tfa : Prop :=
forall ly S (W : world trasegs) regs mem md T,
printf_pre ly S W regs mem md -> vev S < VEV_MAX -> stdout_img (w_H W) mem ->
m_fds md = APSG.fds_std -> AI trasegs (w_H W) (w_A W) md ->
printf_post ly S W regs mem md 1%nat T ->
srealizes trasegs (cfg_at trasegs A_icpt_vprintf regs mem md) (wr ch_stdout line0 T).
Definition printf_next_tfa : Prop :=
forall ly S (W : world trasegs) regs mem md T k,
printf_pre ly S W regs mem md -> vev S < VEV_MAX -> xst k (w_H W) mem -> (1 <= k <= 3)%nat ->
m_fds md = APSG.fds_std -> AI trasegs (w_H W) (w_A W) md ->
printf_post ly S W regs mem md (Datatypes.S k) T ->
srealizes trasegs (cfg_at trasegs A_icpt_vprintf regs mem md) T.
Definition A_EXIT : Z := 0x91100.
Definition exit_leaf_tfa : Prop :=
forall (E' : YQ0j.env) (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs) (code : Z) (k : nat),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 code -> (code = 0 \/ code = 2) -> spZ regs = usp - 48 ->
getr regs 3%bv = w64 TRA_GP -> getr regs 4%bv = w64 TRA_TP ->
mem_ok trasegs E' (mrestrict (w_H W) mem) IMG_L ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI trasegs (w_H W) (w_A W) md -> AR trasegs B ly S W mem md -> top_ok usp ly -> vev S < VEV_MAX ->
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) ->
m_fds md = APSG.fds_std -> m_fs md = fs ->
srealizes trasegs (mkCfg (mkst regs (w64 A_EXIT) mem (seg_rom trasegs)) md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
Definition run_Q_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world trasegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> rrfc_universe B (payload_len data) -> 6 + config_len data <= dlen data ->
let E3 := E_P (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at (sQ (config_len data =? 0) (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes trasegs (mkCfg ms md)
(if payload_len data =? 0 then RUNS data (in_fs inp)
else t_alt2 (ex (if count_mode data then 0 else 2) (in_fs inp)) (RUNS data (in_fs inp))).
Definition loop_L_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (E : YQ0j.env)
(W : world trasegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb pq : sptr) (cap q : Z)
(j r : nat),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> rrfc_universe B (payload_len data) -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew (ELV sp a0 p inp xw xd) k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
bv_unsigned (ew E 161) = sptr_addr B ly pb + 2 + config_len data ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok trasegs E S_L (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = calls data)%nat ->
((payload_len data = 0 /\ q = 0 /\ blocks S = [(pb, cap)])
\/ (0 < payload_len data /\ blocks S = [(pb, cap); (pq, payload_len data)] /\ sptr_addr B ly pq = q)) ->
frames S = [] -> qtightB S ->
AI trasegs (w_H W) (w_A W) md -> AR trasegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
rbud S (Z.of_nat r) 3   -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
((j = 0%nat /\ stdout_img (w_H W) (ms_mem ms)) \/ ((1 <= j)%nat /\ xst j (w_H W) (ms_mem ms))) ->
arodata_ok B (aview trasegs (w_H W) (ms_mem ms)) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes trasegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (r + (j - 1))%nat)) (ex 0 (in_fs inp))).
End c.
