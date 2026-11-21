(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1x.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AD1x.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1x.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's channel-reader fact for fdchan's third conjunct; fdchan's third conjunct, the channel-reader flag, carried in cs_ok (co_rdr) and threaded to the fd sites). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0i YK15.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w AD1w_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition F_STDERR_LO : Z := 0x9d618.  Definition F_STDERR_HI : Z := 0x9d700.
Definition STDERR_MUT (a : Z) : Prop := F_STDERR_LO <= a < F_STDERR_HI.
Definition A_INITFLAGB : Z := A_INITFLAG.
Definition clipX (l : smem) : smem :=
flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1))
(flat_map (clip_out F_STDERR_LO F_STDERR_HI) (flat_map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) l)).
Definition IMG_X : smem := Eval vm_compute in clipX IMG_REGIONS.
Definition IMG_XL : smem := Eval vm_compute in clipX IMG_L.
Definition DIAG_STK : Z := 16384.
Definition A_exit : Z := 0x879fc.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition img_at (H : word -> bool) (m : word -> option byte) (lo hi : Z) : Prop :=
forall a, lo <= a < hi -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Definition est_frame_tfa : Prop :=
forall (H H' : word -> bool) (m m' : word -> option byte),
est H m -> (forall a, STDERR_MUT a -> aview tfibsegs H' m' a = aview tfibsegs H m a) -> est H' m'.
Definition icpt_pre (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ YK0s.ret_ok (getr regs 1%bv) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ sp_window_lo - 128 <= spZ regs <= sp_window_hi /\
ly_top ly - 4112 <= spZ regs <= ly_top ly + 32 /\ ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
(forall a, spZ regs - DIAG_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B).
Definition icpt_post (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ret : Z) (T : TSet) : Prop :=
forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10%bv = w64 ret -> est (w_H W) mem' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DIAG_STK <= a < spZ regs) -> ~ STDERR_MUT a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ STDERR_MUT a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T.
Definition fprintf_s_site_tfa (fmt : Z) (lit1 lit2 : list byte) : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : YP0m.env) (s : Z) (str : list byte) (T : TSet),
icpt_pre ly S W regs mem md ->
getr regs 10%bv = w64 F_STDERR_LO -> getr regs 11%bv = w64 fmt -> getr regs 12%bv = w64 s ->
Z.of_nat (length str) <= 131071 -> ~ In NUL str ->
spZ regs + 128 <= s -> s + Z.of_nat (length str) + 1 < kHighMemEnd ->
YP03.bytes_at (mrestrict (w_H W) mem) s (str ++ [NUL]) ->
(forall a, s + Z.of_nat (length str) < a < s + Z.of_nat (length str) - (s + Z.of_nat (length str)) mod 8 + 8 -> mrestrict (w_H W) mem (Z_to_bv 64 a) <> None) ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md ->
AI tfibsegs (w_H W) (w_A W) md ->
icpt_post ly S W regs mem md (Z.of_nat (length lit1 + length str + length lit2)) T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_fprintf regs mem md) (wr ch_stderr (lit1 ++ str ++ lit2) T).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Definition exit_site_tfa : Prop :=
forall (XI : smem) (E : YP0m.env) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(ly : alayout) (S : astate) (usp d : Z) (fs : Fs) (code : Z) (k : nat),
(XI = IMG_X /\ k = 0%nat) \/ XI = IMG_XL ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 ->
1 <= bv_unsigned (ew E 8) <= 4194303 ->
getr regs 10%bv = w64 code -> (code = 0 \/ code = 2) ->
spZ regs = usp - d -> (d = 48 \/ d = 128) -> YK0s.ret_ok (getr regs 1%bv) ->
getr regs 3%bv = w64 TFIB_GP -> getr regs 4%bv = w64 TFIB_TP ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) XI ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W mem md -> top_ok usp ly -> st_nev S < EV_MAX ->
est (w_H W) mem ->
((k = 0%nat /\ stdout_img (w_H W) mem) \/ ((1 <= k)%nat /\ xst k (w_H W) mem)) ->
((1 <= k)%nat -> fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ->
((1 <= k)%nat -> m_channel_reader md = true) ->
m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 A_exit) mem (seg_rom tfibsegs)) md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
End c.
