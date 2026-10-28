(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d YCe5 YL02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition F_STDERR_LO : Z := 0xa2578.  Definition F_STDERR_HI : Z := 0xa2660.
Definition STDERR_MUT (a : Z) : Prop := F_STDERR_LO <= a < F_STDERR_HI.
Definition A_INITFLAGB : Z := A_INITFLAG.
Definition clipX (l : smem) : smem :=
flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1))
(flat_map (clip_out F_STDERR_LO F_STDERR_HI) (flat_map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) l)).
Definition IMG_X : smem := Eval vm_compute in clipX IMG_REGIONS.
Definition IMG_XL : smem := Eval vm_compute in clipX IMG_L.
Lemma IMG_X_wf : regions_wf IMG_X = true /\ mem_atoms_lt K_M1 IMG_X = true /\ mem_atoms_lt K_M1 IMG_L = true /\ mem_atoms_lt K_M1 IMG_REGIONS = true
/\ IMG_XL = flat_map (clip_out A_INITFLAGB (A_INITFLAGB + 1)) (flat_map (clip_out F_STDERR_LO F_STDERR_HI) IMG_L) /\ length IMG_X = 36%nat
/\ regions_wf IMG_XL = true /\ mem_atoms_lt K_M1 IMG_XL = true /\ length IMG_XL = 36%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition DIAG_STK : Z := 16384.
Definition A_exit : Z := 0x8d604.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
Definition img_at (H : word -> bool) (m : word -> option byte) (lo hi : Z) : Prop :=
forall a, lo <= a < hi -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Definition est_img_tfa : Prop := forall H m, img_at H m F_STDERR_LO F_STDERR_HI -> est H m.
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
Definition fwrite_site_tfa : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : YP0m.env) (p len : Z) (msg : list byte) (T : TSet),
icpt_pre ly S W regs mem md ->
getr regs 10%bv = w64 p -> getr regs 11%bv = w64 len -> getr regs 12%bv = w64 1 -> getr regs 13%bv = w64 F_STDERR_LO ->
Z.of_nat (length msg) = len -> 1 <= len <= 64 -> 0x10568 <= p -> p + len <= 0x20b7c -> (p + len <= 0x1cd09 \/ 0x1cd1e <= p) ->
(forall i, (i < length msg)%nat -> seg_rom tfibsegs (Z_to_bv 64 (p + Z.of_nat i)) = Some (nth i msg NUL)) ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
AI tfibsegs (w_H W) (w_A W) md ->
icpt_post ly S W regs mem md 1 T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_fwrite regs mem md) (wr ch_stderr msg T).
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
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
AI tfibsegs (w_H W) (w_A W) md ->
icpt_post ly S W regs mem md (Z.of_nat (length lit1 + length str + length lit2)) T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_fprintf regs mem md) (wr ch_stderr (lit1 ++ str ++ lit2) T).
Definition refused_site_tfa : Prop :=
forall (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : YP0m.env) (T : TSet),
icpt_pre ly S W regs mem md ->
getr regs 10%bv = w64 F_STDERR_LO -> getr regs 11%bv = w64 0x196bf -> getr regs 12%bv = w64 67108864 ->
mem_ok tfibsegs E (mrestrict (w_H W) mem) IMG_REGIONS ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
AI tfibsegs (w_H W) (w_A W) md ->
icpt_post ly S W regs mem md (Z.of_nat (length msg_refused)) T ->
srealizes tfibsegs (cfg_at tfibsegs A_icpt_fprintf regs mem md) (wr ch_stderr msg_refused T).
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
m_fs md = fs ->
srealizes tfibsegs (mkCfg (mkst regs (w64 A_exit) mem (seg_rom tfibsegs)) md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
End c.
