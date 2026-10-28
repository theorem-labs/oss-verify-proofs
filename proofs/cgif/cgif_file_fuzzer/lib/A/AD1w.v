(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d YCe5 YL02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK00 YI00 YI16.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From Stdlib Require Import Permutation.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
Lemma blk_shift : forall H m buf len data off,
blk H m buf len data -> 0 <= off <= len -> blk H m (buf + off) (len - off) (skipn (Z.to_nat off) data).
Proof.
intros H m buf len data off HB Hoff i Hi. rewrite nth_error_skipn, <- Z.add_assoc, (HB (off + i)) by lia.
f_equal. rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.
Lemma garr8_of_blk : forall H m q (pl : list byte),
blk H m q (Z.of_nat (length pl)) pl -> garr8 tfibsegs (mrestrict H m) q (map (fun b : byte => bv_unsigned b) pl).
Proof.
intros H m q pl HB j Hj. rewrite length_map in Hj.
assert (Hn : nth j (map (fun b : byte => bv_unsigned b) pl) 0 = bv_unsigned (nth j pl (Z_to_bv 8 0))).
{ rewrite <- (map_nth (fun b : byte => bv_unsigned b)). reflexivity. }
rewrite Hn. pose proof (u8_range (nth j pl (Z_to_bv 8 0))) as R.
split; [| lia].
intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold mbyte. pose proof (HB (Z.of_nat j) ltac:(lia)) as X. rewrite Nat2Z.id in X. rewrite X.
rewrite (nth_error_nth' pl (Z_to_bv 8 0) Hj). f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256 R).
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Definition tail_at (ss : sstate) (E : YP0m.env) (sp : word) (inp : ProcInput) (a0 p data : list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (pb : sptr) (cap : Z) : Prop :=
st_ok tfibsegs E ss (restrict (w_H W) ms) /\
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb /\ bv_unsigned (ew E A_LEN) = dlen data /\
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) /\
AI tfibsegs (w_H W) (w_A W) md /\ AR tfibsegs B ly S W (ms_mem ms) md /\ top_ok (bv_unsigned sp) ly /\
blocks S = [(pb, cap)] /\ st_nev S <= 64 /\ 65536 <= cap <= 2 ^ 26 /\ dlen data < cap /\
blk (w_H W) (ms_mem ms) (sptr_addr B ly pb) (dlen data) data /\
m_fs md = in_fs inp /\ m_fds md = APSG.fds_std /\ drv_minv S cap (dlen data) /\
FINV ly (w_H W) (ms_mem ms)    .
Definition short_leaf_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> dlen data <= 5 ->
tail_at S_SHORT (havoc (ELV sp a0 p inp xw xd) K_M1 ws) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag msg_short (in_fs inp)).
Definition overrun_leaf_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 <= dlen data < 6 + config_len data ->
tail_at S_OVR (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (diag msg_overrun (in_fs inp)).
Definition post_P_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
tail_at S_P (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Definition lib_pre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ YK0s.ret_ok (getr regs 1%bv) /\ raZ regs = RA_LLVMF /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ spZ regs + 32 <= ly_top ly <= spZ regs + 4128 /\
ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
(forall a, spZ regs - LLVMF_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
s0Z regs < alloc_ceiling /\
qtight S                                    .
Definition lib_site_x : Prop :=
forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n (pl : list byte) (K : lleaf -> TSet),
lib_pre ly S W regs mem md ->
getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
((n = 0 /\ p = A_EMPTY_tfa) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
n = Z.of_nat (length pl) -> garr8 tfibsegs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
FINV ly (w_H W) mem ->
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Namei.fd_names_path (m_fds md) YI16.sink_path = false ->
Fs.fs_sorted (m_fs md) = true ->
AI tfibsegs (w_H W) (w_A W) md ->
(forall (l : lleaf) (W' : world tfibsegs) (c' : config),
wle W W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
YCbq.ajournal tfibsegs B LLVMF_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10%bv = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
Namei.fd_names_path (m_fds md') YI16.sink_path = false /\
FINV ly' (w_H W') mem' /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i))) ->
srealizes tfibsegs c' (K l)) ->
srealizes tfibsegs (cfg_at tfibsegs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
Definition free_null_site_tfa : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
drv_pre B ly S W regs mem md -> getr regs 10%bv = w64 0 ->
In [pc_free_ra0 (as_code B); raZ regs] (as_universe B) -> In [pc_free_ra0 (as_code B)] (as_universe B) ->
SRr tfibsegs W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' trc tr,
In trc (as_universe B) /\ apath (free PNull trc S) tr (tt, S') /\
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B ASTACK ly S W regs mem md (fun _ => False) ly' S' W' regs' mem' md').
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition STDOUT_MUT (a : Z) : Prop := (STDOUT_LO <= a < STDOUT_HI) \/ (SOBUF_LO <= a < SOBUF_HI).
Definition stdout_img (H : word -> bool) (m : word -> option byte) : Prop :=
forall a, STDOUT_LO <= a < STDOUT_HI -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Definition xst_frame_tfa : Prop :=
forall k (H H' : word -> bool) (m m' : word -> option byte),
xst k H m -> (forall a, STDOUT_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> xst k H' m'.
Definition A_icpt_vprintf : Z := 0x41920.
Definition RA_EMIT : Z := 0x80484.
Definition A_FMT_D : Z := 0x147ea.
Definition PF_STK : Z := 9216.
Definition printf_pre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ raZ regs = RA_EMIT /\
spZ regs mod 16 = 0 /\ sp_window_lo - 288 <= spZ regs /\ ly_top ly - 4208 <= spZ regs <= ly_top ly - 128 /\
spZ regs + 288 <= sp_window_hi /\ ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
arodata_ok B (aview tfibsegs (w_H W) mem) /\
(forall a, spZ regs - PF_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
getr regs 10%bv = w64 A_FMT_D /\ getr regs 11%bv = w64 (spZ regs + 24) /\
rdword (aview tfibsegs (w_H W) mem) (spZ regs + 24) = Some 0.
Definition printf_post (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(k' : nat) (T : TSet) : Prop :=
forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' -> getr regs' 10%bv = w64 2 ->
xst k' (w_H W) mem' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - PF_STK <= a < spZ regs) -> ~ STDOUT_MUT a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDOUT_MUT a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T.
Definition printf_first_tfa : Prop :=
forall ly S (W : world tfibsegs) regs mem md T,
printf_pre ly S W regs mem md -> st_nev S < EV_MAX -> stdout_img (w_H W) mem ->
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) ->
AI tfibsegs (w_H W) (w_A W) md ->
printf_post ly S W regs mem md 1%nat T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_vprintf regs mem md) (wr ch_stdout line0 T).
Definition printf_next_tfa : Prop :=
forall ly S (W : world tfibsegs) regs mem md T k,
printf_pre ly S W regs mem md -> st_nev S < EV_MAX -> xst k (w_H W) mem -> (1 <= k <= 3)%nat ->
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) ->
AI tfibsegs (w_H W) (w_A W) md ->
printf_post ly S W regs mem md (Datatypes.S k) T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_vprintf regs mem md) T.
Definition A_EXIT : Z := 0x8cf04.
Definition exit_leaf_tfa : Prop :=
forall (E' : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp : Z) (fs : Fs) (code : Z) (k : nat),
bv_unsigned (ew E' 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E' 8) <= 4194303 ->
getr regs 10%bv = w64 code -> (code = 0 \/ code = 2) -> spZ regs = usp - 48 ->
getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E' (mrestrict (w_H W) mem) IMG_L ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) ->
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 A_EXIT) mem (seg_rom tfibsegs)) md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
Definition run_Q_tfa : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
let E3 := E_P (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at (sQ (config_len data =? 0) (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Lemma finv_printf : forall (HB : TfibSyms B) (ARL : AR_laws tfibsegs B) ly S (W : world tfibsegs) mem md (mem' : word -> option byte) usp splo,
AR tfibsegs B ly S W mem md -> top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= splo <= usp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (splo - PF_STK <= a < splo) -> ~ STDOUT_MUT a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
FINV ly (w_H W) mem -> FINV ly (w_H W) mem'.
Proof.
intros HB ARL ly S W mem md mem' usp splo HAR (_ & Hlo & Hhi & HCT) Ulo Uhi Hsplo Hfr HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_off B ly S W mem md mem' (fun a => splo - PF_STK <= a < splo) STDOUT_MUT HAR Hfr); [|exact HFI].
intros a Ha. split.
- apply (finv_avoids_stack B ly S W mem md (splo - PF_STK) splo a HAR); [| | | exact Ha].
+ rewrite Hlo. unfold ASAN_CEIL, stack_max_size, PF_STK in *. lia.
+ rewrite Hhi. unfold kHighMemEnd, sp_window_hi in *. lia.
+ unfold sp_window_lo, PF_STK in *. lia.
- intros [Hso | Hso]; revert Hso.
+ apply (finv_avoids_img B ly S W mem md STDOUT_LO STDOUT_HI a HAR); [intros x Hx; apply AD1y.in_img_hull; unfold STDOUT_LO, STDOUT_HI in Hx; lia | vm_compute; reflexivity | exact Ha].
+ apply (finv_avoids_img B ly S W mem md SOBUF_LO SOBUF_HI a HAR); [intros x Hx; apply AD1y.in_img_hull; unfold SOBUF_LO, SOBUF_HI in Hx; lia | vm_compute; reflexivity | exact Ha].
Qed.
Lemma run_tail_eq : forall m fs, t_eq (wr ch_stdout (concat (repeat line0 m)) (ex 0 fs)) (run_tail m fs).
Proof.
intros [|m] fs; cbn [run_tail repeat concat]; [| apply t_eq_refl].
unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil.
Qed.
Definition MDI (md : Model) (fs : Fs) : Prop :=
(forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) /\ Namei.fd_names_path (m_fds md) YI16.sink_path = false /\
m_fs md = fs /\ Fs.fs_sorted fs = true.
Definition loop_tgt (pl : list byte) (ncalls j r : nat) (fs : Fs) : TSet :=
match j with O => run_shape pl r fs | S _ => lib_iter pl r (run_tail (ncalls - 1)) fs end.
Definition loop_L_x : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (E : YP0m.env)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb pq : sptr) (cap q : Z)
(j r : nat) (fs : Fs),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew (ELV sp a0 p inp xw xd) k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
bv_unsigned (ew E 161) = sptr_addr B ly pb + 2 + config_len data ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok tfibsegs E S_L (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = calls data)%nat ->
((payload_len data = 0 /\ q = 0 /\ blocks S = [(pb, cap)])
\/ (0 < payload_len data /\ blocks S = [(pb, cap); (pq, payload_len data)] /\ sptr_addr B ly pq = q)) ->
(0 < payload_len data -> blk (w_H W) (ms_mem ms) q (payload_len data) (payload data)) ->
frames S = [] -> qtight S ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
st_nev S + EV_LIB * Z.of_nat r + 3 <= EV_MAX -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
((j = 0%nat /\ stdout_img (w_H W) (ms_mem ms)) \/ ((1 <= j)%nat /\ xst j (w_H W) (ms_mem ms))) ->
arodata_ok B (aview tfibsegs (w_H W) (ms_mem ms)) ->
FINV ly (w_H W) (ms_mem ms) -> MDI md fs ->
srealizes tfibsegs (mkCfg ms md) (loop_tgt (payload data) (calls data) j r fs).
End c.
