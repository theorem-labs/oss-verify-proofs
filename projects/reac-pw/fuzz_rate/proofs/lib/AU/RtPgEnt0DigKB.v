(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bBase.v at 21da95a5fcd3; its block post w7_post, w7_post_of_run and w7_kept_run as rt7bd_post, rt7bd_post_of_run and rt7bd_kept_run over image B's segments. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0DigK.v at 21da95a5fcd3; image B's code (P1 0x8152c .. 0x8153c, the token run 0x81540 .. 0x81604 with its two UBSan trap tests 0x81540 and 0x815f8 and the read-only cell R+0xd8, P2 0x81608), registers (&r in s7, &ch in s2, the shadow offset in s4, the frame's shadow base in s3, the multiplier in s5, t0 = 4 / t2 = 10 / t3 = 9 pinned and kept), the class-4 frame for locals and lib/AU/RtPgMemB.v's shadow row; no check on ch's stores; names rt7d_ -> rt7bd_. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0DigKB.v, with its module paths changed; 6 of its 335 lines of code are new or changed and 43 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0DigK.v at 21da95a5fcd3; image B's code (P1 0x8152c .. 0x8153c, the token run 0x81540 .. 0x81604 with its two UBSan trap tests 0x81540 and 0x815f8 and the read-only cell R+0xd8, P2 0x81608), registers (&r in s7, &ch in s2, the shadow offset in s4, the frame's shadow base in s3, the multiplier in s5, t0 = 4 / t2 = 10 / t3 = 9 pinned and kept), the class-4 frame for locals and lib/AU/RtPgMemB.v's shadow row; no check on ch's stores; the block post is lib/AU/RtPgW7bBaseB.v's w7b_post; names rt7d_ -> rt7bd_, w7_ -> w7b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the kit of the DIG block of
   ent_build's case 0 (pod.h:237-246, c < 200), the walk from lib/AU/RtPgEnt0DefB.v rt7b_cut_DIG at 0x8152c to G =
   0x8160c. Proves no function (kind: segment lemma).

   THE CODE AND ITS THREE RUNS. A run that stores a shadow byte is a plain engine run with the frame's shadow byte
   writable; a run that passes an instrumented check is a token run (lib/Reusable/YCbn.v) with no shadow byte in its
   regions and r and ch listed in the shadow entries rt7bd_SH. So the block is three runs:
     P1  0x8152c .. 0x8153c  plain: a2 := 0, a6 := c & 63, `sb t0,28(s3)` (r's granule, shadow_addr F + 28,
                             := 0x04 with t0 = 4), a1 := s7, a7 := s7 (s7 = &r = F + 0xe0)
     T   0x81540 .. 0x81604  token: the digit loop (the UBSan bound test `bne a2,t0,+8; j 0x83098` with t0 = 4;
                             r[k] := '0' + v mod 10 at s7 + k with its store check `lb; bnez -> 0x8159c`, whose
                             slow block `andi a6,a1,7; blt a6,a2 -> 0x8156c` always runs: r's shadow byte is 0x04;
                             v / 10 by `slli 32; mulhu s5; srli 35`; `bltu t3,a5` with t3 = 9), the reverse copy
                             ch[i] := r[k-1-i] (the read check of r with the slow block 0x815e0; ch's stores carry
                             no check), and the NUL: a0 := zext32 k, `ld a1,0xd8(s1)` (the cell R+0xd8 = ~&ch),
                             the UBSan test `bgeu a1,a0,+8; j 0x83098`, ch[k] := 0 (no check)
     P2  0x81608             plain: `sb s8,28(s3)` with s8 = -8 (r out of scope)
   The token run takes v = c mod 64 as a literal (one engine run per v < 64, lib/AU/RtPgEnt0DigT0B.v .. T3B.v):
   then the bound test and every loop branch are decided and every byte of r and ch is a literal chunk. The cell
   R+0xd8 is a read-only region whose chunk is the atom 32 (the run's one extra value), bounded by the closed
   numerals [2^63, 2^64 - 1] (~&ch with &ch < 2^63), so the engine decides `bgeu a1,a0` against k < 4 by itself.
   The run's obligations are the one-byte checks of r, paid by lib/AU/RtPgMemB.v rtmb_B_ra_r from the frame's
   shadow row rt7b_PR.
   THE ENGINE STATES. Atom 20 = s4 = K is the token's shadow base; atom 23 = s7 = F + 0xe0 bases r's 4 bytes,
   atom 18 = s2 = F + 0xa0 bases ch's 24, atom 9 = s1 = R the cell; r and ch are 32-aligned (the frame for locals is
   a class-4 side-stack frame, F mod 32 = 0). The plain runs' one region is shadow_addr F + 28, based at atom 19 =
   s3. t0, t2, t3 and s5 are pinned to their literals and kept (rt7bd_pinsT); the token run changes a0 .. a7 only. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgStepsB RtPgSegB RtPgEnt0DefB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition RT7BD_P1 : Z := 0x8152c.     (* = RT7B_DIG: `li a2,0` *)
Definition RT7BD_LOOP : Z := 0x81540.   (* the digit loop's head: the bound test `bne a2,t0,+8` *)
Definition RT7BD_P2 : Z := 0x81608.     (* after the NUL store: `sb s8,28(s3)` *)
Definition RT7BD_G : Z := 0x8160c.      (* = RSB_G *)
Lemma rt7bd_pcs : RT7BD_P1 = RT7B_DIG /\ RT7BD_G = RSB_G.
Proof. split; reflexivity. Qed.

(* ======================================== the engine states ======================================== *)
(* the plain runs: the frame's shadow byte of r's granule, based at s3 = shadow_addr F *)
Definition rt7bd_rRow : YP09.region := YP09.mkRegion (Some 19%nat) 28 29 28 29 [].
Definition rt7bd_ssP (pc : Z) : sstate := mkSS pc sr_atoms [rt7bd_rRow] None (mkFacts [] [] []).
(* s8 = -8 as the 64-bit word P2 stores the low byte of *)
Definition RT7BD_M8 : Z := 18446744073709551608.
(* the token run: r[4] at s7 = F + 0xe0 and ch[24] at s2 = F + 0xa0, both writable; the cell R+0xd8 read-only,
   holding the extra atom 32; s4 = K exactly *)
Definition RT7BD_SB : Z := 0x7fff8000.
Definition RT7BD_Bx : sv := SOff 20 0.
Definition RT7BD_Bspan : Z * Z := (RT7BD_SB, RT7BD_SB + 2 ^ 44 - 1).
Definition rt7bd_rR : YP09.region := YP09.mkRegion (Some 23%nat) 0 4 0 4 [].
Definition rt7bd_rCh : YP09.region := YP09.mkRegion (Some 18%nat) 0 24 0 24 [].
Definition rt7bd_rD8 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xd8 0xe0 0 0 [YP09.mkChunk 0xd8 (CVal 8 (SOff 32 0))].
Definition RT7BD_HI : Z := 2 ^ 47 - 16384.
(* every bound a closed numeral *)
Definition rt7bd_fT : facts :=
mkFacts [(18%nat, mkAF 4096 RT7BD_HI 5); (20%nat, mkAF RT7BD_SB RT7BD_SB 0); (23%nat, mkAF 4096 RT7BD_HI 5);
         (32%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] [].
(* r's and ch's bytes, apart from the shadow band: r's checks load r's shadow byte as a token, and ch's write window
   must be one of these (YCbn.v cells_safe_b) though ch's stores carry no check *)
Definition rt7bd_SH : list shent := [mkSHE 23 4 0; mkSHE 18 24 0].
Definition rt7bd_extra (d : Z) : list word := [Z_to_bv 64 d].
Definition rt7bd_ss0 : sstate := mkSS RT7BD_LOOP sr_atoms [rt7bd_rR; rt7bd_rCh; rt7bd_rD8] None rt7bd_fT.
(* the loop's eight values: a2 = k = 0, a6 = v, a1 = a7 = &r, t0 = 4, t2 = 10, t3 = 9, s5 = the multiplier *)
Definition rt7bd_ssT (v : Z) : sstate :=
mkSS RT7BD_LOOP
  (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
     12%bv (SLit 0)) 16%bv (SLit v)) 11%bv (SOff 23 0)) 17%bv (SOff 23 0))
     5%bv (SLit 4)) 7%bv (SLit 10)) 28%bv (SLit 9)) 21%bv (SLit RSB_MULT10))
  [rt7bd_rR; rt7bd_rCh; rt7bd_rD8] None rt7bd_fT.

(* the registers the token run changes (a0 .. a7, the two slow blocks' scratch included) *)
Definition rt7bd_clobT : list (bv 5) := [10; 11; 12; 13; 14; 15; 16; 17]%bv.
(* the registers it holds pinned to the literal they hold, and so keeps *)
Definition rt7bd_pinsT : list (bv 5 * sv) :=
  [((5%bv : bv 5), SLit 4); ((7%bv : bv 5), SLit 10); ((28%bv : bv 5), SLit 9); ((21%bv : bv 5), SLit RSB_MULT10)].
(* the bytes it writes: r and ch *)
Definition rt7bd_wT (F : Z) : Z -> Prop := fun a => F + 0xe0 <= a < F + 0xe4 \/ F + 0xa0 <= a < F + 0xb8.
(* the byte the plain runs write *)
Definition rt7bd_wP (F : Z) : Z -> Prop := fun a => a = shadow_addr F + 28.

(* ======================================== reading a region back ======================================== *)
(* a one-byte literal chunk at offset o holding z *)
Definition rt7bd_lit1 (c : YP09.chunk) (o z : Z) : bool :=
match c with
| YP09.mkChunk o' (CVal w (SLit z')) => (w =? 1)%N && (o' =? o) && (z' =? z)
| _ => false
end.
(* region i is based at atom n and holds the bytes l from its offset 0 on, each as a one-byte literal chunk *)
Definition rt7bd_bytes_chk (ss : sstate) (i n : nat) (l : list byte) : bool :=
match nth_error (ss_mem ss) i with
| Some r =>
    match YP09.r_base r with
    | Some n' => Nat.eqb n' n &&
        forallb (fun j => existsb (fun c => rt7bd_lit1 c (Z.of_nat j) (bv_unsigned (nth j l (Z_to_bv 8 0))))
                   (YP09.r_chunks r)) (seq 0 (length l))
    | None => false
    end
| None => false
end.

Lemma rt7bd_lit1_ok : forall c o z, rt7bd_lit1 c o z = true -> c = YP09.mkChunk o (CVal 1 (SLit z)).
Proof.
intros [o' cv] o z H. unfold rt7bd_lit1 in H.
destruct cv as [w e | len | len | d s len]; cbv beta iota in H; try discriminate H.
destruct e as [z' | | | | | | | | | |]; cbv beta iota in H; try discriminate H.
apply andb_prop in H as [H Hz]. apply andb_prop in H as [Hw Ho].
apply N.eqb_eq in Hw. apply Z.eqb_eq in Ho. apply Z.eqb_eq in Hz. subst. reflexivity.
Qed.

(* the pinned registers hold their literals *)
Lemma rt7bd_pins_ok : forall E (regs : bvmap 5 word),
getr regs 5 = w64 4 -> getr regs 7 = w64 10 -> getr regs 28 = w64 9 -> getr regs 21 = w64 RSB_MULT10 ->
forall r e, In (r, e) rt7bd_pinsT -> sv_denot E e = getr regs r.
Proof.
intros E regs H5 H7 H28 H21 r e Hin. cbv [rt7bd_pinsT In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; symmetry; assumption|]).
destruct Hin.
Qed.

(* ~x as the cell R+0xd8 holds it, for a pointer x below 2^63 *)
Lemma rt7bd_lnot_range : forall x, 0 <= x < 2 ^ 63 ->
9223372036854775808 <= Z.lnot x mod 2 ^ 64 <= 18446744073709551615.
Proof.
intros x Hx. unfold Z.lnot.
replace (Z.pred (- x)) with ((2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma rt7bd_bytes_of : forall E ss (H : word -> bool) ms i n b (l : list byte),
st_ok rsegs E ss (restrict H ms) -> bv_unsigned (ew E n) = b -> rt7bd_bytes_chk ss i n l = true ->
rtmb_bytes rsegs H (ms_mem ms) b l.
Proof.
intros E ss H ms i n b l HS Hb Hc. unfold rt7bd_bytes_chk in Hc.
destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
destruct r as [rb lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_chunks] in Hc.
destruct rb as [n'|]; [|discriminate].
apply andb_prop in Hc as [Hn Hc]. apply Nat.eqb_eq in Hn. subst n'.
pose proof (rtsb_region_nth E ss ms i _ H HS Hi) as Hr.
apply (rtmb_bytes_aview rsegs). intros j Hj.
rewrite forallb_forall in Hc. specialize (Hc j ltac:(apply in_seq; lia)).
apply existsb_exists in Hc as (c & Hin & Hl).
apply rt7bd_lit1_ok in Hl. subst c.
set (x := nth j l (Z_to_bv 8 0)).
pose proof (bv_unsigned_in_range 8 x) as Hx. change (bv_modulus 8) with 256 in Hx.
pose proof (rtsb_chunks E _ n b cs lo hi wlo whi Hr Hb _ Hin) as Hck.
pose proof (val_of_chunk_ok rsegs E _ b (Z.of_nat j) 1 (SLit (bv_unsigned x)) (bv_unsigned x) Hck eq_refl
  ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(cbn; lia)) as Hv.
exact (rtmb_val1_aview rsegs H (ms_mem ms) (b + Z.of_nat j) (bv_unsigned x) Hv Hx).
Qed.

(* a register pinned to a literal it holds *)
Lemma rt7bd_pin : forall E ss ms (r : bv 5) z,
st_ok rsegs E ss ms -> bv_eqb r 0 = false -> getr (ms_regs ms) r = Z_to_bv 64 z ->
st_ok rsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. exact (st_ok_pin_lit rsegs). Qed.

Section d.
Variable B : asyms.

(* ---- the frame for locals at a block's start (class 4: 1024 bytes, 128 shadow bytes) ---- *)
Lemma rt7bd_frame : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
In (4, pos) (frames Sc) /\ F mod 32 = 0 /\ F mod 8 = 0 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\
alloc_ceiling <= 0x7fffff800000 /\
0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
(forall i, 0 <= i < 128 -> apresent (w_H W) memc (shadow_addr F + i)) /\
(forall a, F <= a < F + 1024 -> apresent (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & HFapp & HFob & HFsh).
rewrite <- HF in HF32, HFapp, HFob, HFsh. change (fs_frame_bytes 4) with 1024 in HFapp, HFob, HFsh.
change (1024 / 8) with 128 in HFsh.
destruct (rtsb_fbounds F HF32 HFapp) as (B0 & B1 & B2 & B3 & B4 & _).
pose proof asan_consts as (C1 & _).
assert (HF8 : F mod 8 = 0).
{ destruct (rtsb_fdiv F HF32) as [E1 _]. rewrite E1. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring.
  apply Z_mod_mult. }
split; [exact Hin4|]. split; [exact HF32|]. split; [exact HF8|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B4|].
split; [intros i Hi; exact (proj1 (HFsh i Hi))|].
intros a Ha. exact (proj1 (HFob a Ha)).
Qed.

(* ---- the shadow entries of the token run: r's 4 bytes and ch's 24, apart from the shadow band ---- *)
Lemma rt7bd_shok : forall lyc Sc W memc mdc (regs : bvmap 5 word) extra M F pos,
AR rsegs B lyc Sc W memc mdc -> In (4, pos) (frames Sc) -> F = frame_addr lyc 4 pos ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 23 = w64 (F + 0xe0) -> getr regs 18 = w64 (F + 0xa0) ->
0 <= F -> F + 1024 < 2 ^ 64 ->
sh_ok rsegs RT7BD_Bx rt7bd_SH (Ereg regs extra) M.
Proof.
intros lyc Sc W memc mdc regs extra M F pos HAR Hin HF H20 H23 H18 HF0 HF1.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (U20 : U (Ereg regs extra) RT7BD_Bx = SHADOW_OFF).
{ unfold RT7BD_Bx. apply U_atom; [rewrite (ew_Ereg_nat regs extra 20 20%bv eq_refl); exact H20 | exact shadow_off_range]. }
assert (U23 : U (Ereg regs extra) (SOff 23 0) = F + 0xe0).
{ apply U_atom; [rewrite (ew_Ereg_nat regs extra 23 23%bv eq_refl); exact H23 | lia]. }
assert (U18 : U (Ereg regs extra) (SOff 18 0) = F + 0xa0).
{ apply U_atom; [rewrite (ew_Ereg_nat regs extra 18 18%bv eq_refl); exact H18 | lia]. }
constructor; [|constructor; [|constructor]].
- refine (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc _ RT7BD_Bx 23 (F + 0xe0) 4 pos 0 4 M HAR Hin U20 U23 _ _ _);
    rewrite <- ?HF; change (fs_frame_bytes 4) with 1024; lia.
- refine (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc _ RT7BD_Bx 18 (F + 0xa0) 4 pos 0 24 M HAR Hin U20 U18 _ _ _);
    rewrite <- ?HF; change (fs_frame_bytes 4) with 1024; lia.
Qed.

(* ---- the entry state of the token run ---- *)
Lemma rt7bd_T_entry : forall (W : world rsegs) memc (regs : bvmap 5 word) F R d v,
F mod 32 = 0 -> 4096 <= F -> F + 1024 <= RT7BD_HI -> F + 1024 <= R -> R + 0xe0 <= 2 ^ 63 ->
(forall a, F <= a < F + 1024 -> apresent (w_H W) memc a) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 d -> 9223372036854775808 <= d <= 18446744073709551615 ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 23 = w64 (F + 0xe0) -> getr regs 18 = w64 (F + 0xa0) ->
getr regs 9 = w64 R ->
getr regs 12 = w64 0 -> getr regs 16 = w64 v -> getr regs 11 = w64 (F + 0xe0) -> getr regs 17 = w64 (F + 0xe0) ->
getr regs 5 = w64 4 -> getr regs 7 = w64 10 -> getr regs 28 = w64 9 -> getr regs 21 = w64 RSB_MULT10 ->
st_ok rsegs (Ereg regs (rt7bd_extra d)) (rt7bd_ssT v)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7BD_LOOP) memc (seg_rom rsegs))).
Proof.
intros W memc regs F R d v HF32 HF0 HF1 HFR HR1 HFp Hval Hd H20 H23 H18 H9 H12 H16 H11 H17 H5 H7 H28 H21.
unfold RT7BD_HI in HF1.
assert (HFa : (F + 0xa0) mod 32 = 0).
{ rewrite Z.add_mod by lia. rewrite HF32. reflexivity. }
assert (HFe : (F + 0xe0) mod 32 = 0).
{ rewrite Z.add_mod by lia. rewrite HF32. reflexivity. }
assert (X23 : ew (Ereg regs (rt7bd_extra d)) 23 = Z_to_bv 64 (F + 0xe0))
  by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (U23 : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 23) = F + 0xe0)
  by (rewrite X23; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 18) = F + 0xa0).
{ rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18. unfold w64. apply unsigned_lit_small. lia. }
assert (U20 : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 20) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20. unfold w64. apply unsigned_lit_small.
  exact shadow_off_range. }
assert (U9 : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (rt7bd_extra d)) 32 = Z_to_bv 64 d) by exact (ew_Ereg_extra regs _ 0).
assert (U32 : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 32) = d) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HD8 : region_ok rsegs (Ereg regs (rt7bd_extra d)) (mrestrict (w_H W) memc) rt7bd_rD8).
{ unfold rt7bd_rD8. apply (rtmb_ro_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia |].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs (Ereg regs (rt7bd_extra d)) (mrestrict (w_H W) memc) R 0xd8 8 (SOff 32 0) d).
  - apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r. rewrite !unsigned_lit_small by lia.
    unfold zcanon, M64. apply Z.mod_small. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - exact Hval. }
assert (HS0 : st_ok rsegs (Ereg regs (rt7bd_extra d)) rt7bd_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7BD_LOOP) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [exact HD8 | constructor]]].
    + apply (rtmb_rw_region rsegs _ _ _ 23%nat (F + 0xe0)); [exact U23 | lia | lia | | constructor].
      intros o Ho. apply HFp. lia.
    + apply (rtmb_rw_region rsegs _ _ _ 18%nat (F + 0xa0)); [exact U18 | lia | lia | | constructor].
      intros o Ho. apply HFp. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [rt7bd_rR rt7bd_rCh rt7bd_rD8 YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23, U18, U9.
    repeat split; lia.
  - split; [|split; exact I]. cbn [rt7bd_ss0 rt7bd_fT f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U20, U23, U32. unfold RT7BD_SB, SHADOW_OFF, RT7BD_HI. change (2 ^ 0) with 1. change (2 ^ 5) with 32.
    rewrite !Z.mod_1_r, HFa, HFe. repeat split; lia. }
assert (D23 : sv_denot (Ereg regs (rt7bd_extra d)) (SOff 23 0) = Z_to_bv 64 (F + 0xe0))
  by exact (rtsb_den_atom _ 23 (F + 0xe0) X23 ltac:(lia)).
pose proof (rt7bd_pin _ _ _ 12%bv 0 HS0 eq_refl H12) as HS1. clear HS0.
pose proof (rt7bd_pin _ _ _ 16%bv v HS1 eq_refl H16) as HS2. clear HS1.
pose proof (st_ok_pin_sv rsegs _ _ _ 11%bv (SOff 23 0) HS2 eq_refl (eq_trans D23 (eq_sym H11))) as HS3. clear HS2.
pose proof (st_ok_pin_sv rsegs _ _ _ 17%bv (SOff 23 0) HS3 eq_refl (eq_trans D23 (eq_sym H17))) as HS4. clear HS3.
pose proof (rt7bd_pin _ _ _ 5%bv 4 HS4 eq_refl H5) as HS5. clear HS4.
pose proof (rt7bd_pin _ _ _ 7%bv 10 HS5 eq_refl H7) as HS6. clear HS5.
pose proof (rt7bd_pin _ _ _ 28%bv 9 HS6 eq_refl H28) as HS7. clear HS6.
pose proof (rt7bd_pin _ _ _ 21%bv RSB_MULT10 HS7 eq_refl H21) as HS8. clear HS7.
exact HS8.
Qed.

(* ---- the block statement of the token run, for one value v of c mod 64 ---- *)
Definition rt7bd_T_stmt (v : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (F pos R d : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 23 = w64 (F + 0xe0) -> getr regs 18 = w64 (F + 0xa0) ->
getr regs 9 = w64 R -> F + 1024 <= R -> R + 0xe0 <= 2 ^ 63 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 d -> 9223372036854775808 <= d <= 18446744073709551615 ->
getr regs 12 = w64 0 -> getr regs 16 = w64 v -> getr regs 11 = w64 (F + 0xe0) -> getr regs 17 = w64 (F + 0xe0) ->
getr regs 5 = w64 4 -> getr regs 7 = w64 10 -> getr regs 28 = w64 9 -> getr regs 21 = w64 RSB_MULT10 ->
rt_fsh rsegs (w_H W) memc F rt7b_PR ->
SRr rsegs W (cfg_at rsegs RT7BD_LOOP regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7BD_P2 regs memc mdc rt7bd_clobT (rt7bd_wT F)
 (fun _ mem2 => rtmb_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 v ++ [Cursor.NUL]))).
End d.
End b.

(* ======================================== the tactic of one token run ======================================== *)
(* one obligation: the one-byte check of r[j], from the row rt7b_PR *)
Ltac rt7bd_obl F X20 X23 Hfsh HF8 :=
  cbn [ms_mem mkst]; unfold RT7BD_Bx;
  change (rd_of rsegs (mrestrict ?H ?m)) with (aview rsegs H m);
  rewrite (U_atom _ 20 SHADOW_OFF X20 shadow_off_range);
  lazymatch goal with
  | |- range_addressable _ _ (U _ (SOff 23 ?j)) _ =>
      rewrite (U_atom_off _ 23 (F + 0xe0) j X23 ltac:(lia) ltac:(lia));
      replace (F + 0xe0 + j) with (F + RTMB_R + j) by (unfold RTMB_R; lia);
      apply (rtmb_B_ra_r rsegs _ _ F true true false false true false j 1 Hfsh HF8); lia
  end.
(* the write rights of r and ch: the frame for locals' own bytes; the cell R+0xd8 grants none *)
Ltac rt7bd_awr U23F U18F Hown :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  eapply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 23%nat _ 0xe0); [reflexivity | exact U23F | exact Hown | cbn; lia | cbn; lia |];
  eapply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 18%nat _ 0xa0); [reflexivity | exact U18F | exact Hown | cbn; lia | cbn; lia |];
  apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_nil.
(* the leaf: the journal, the I/O state, the registers outside rt7bd_clobT, the bytes outside r and ch, ch's text *)
Ltac rt7bd_leaf B regs W memc F d U23 U18 HAE H5 H7 H28 H21 :=
  lazymatch goal with
  | HS : st_ok _ ?E' ?ssf (restrict (w_H W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFr : frame_of _ _ (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ?ms)),
    HG : mem_grows _ _ |- _ =>
    assert (HA : env_agree 32 (Ereg regs (rt7bd_extra d)) E') by env_agree_chain HAE;
    eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ];
    [ eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs (rt7bd_extra d) (w_H W) _ rt7bd_pinsT HS HA);
      [ exact (rt7bd_pins_ok E' regs H5 H7 H28 H21) | vm_compute; reflexivity ]
    | let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
      intros a Ha Hz;
      refine (w7b_kept_run (rt7bd_wT F) _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr _ a Ha Hz);
      let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros x (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      repeat (destruct Hin as [<-|Hin];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U23, ?U18 in Hr; unfold rt7bd_wT; lia |]);
      destruct Hin
    | cbv beta;
      apply (rt7bd_bytes_of E' ssf (w_H W) ms 1 18 (F + 0xa0));
      [ exact HS | rewrite (proj1 HA 18%nat ltac:(lia)); exact U18 | vm_compute; reflexivity ] ]
  end.
Ltac rt7bd_T_tac :=
  let B := lazymatch goal with |- rt7bd_T_stmt ?B _ => B end in
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F pos R d HJ Hown HF H20 H23 H18 H9 HFR HR1
    Hval Hd H12 H16 H11 H17 H5 H7 H28 H21 Hfsh;
  pose proof (AR_laws_ok rsegs B) as LAWS;
  pose proof rtsb_wx as Hwx; pose proof rtsb_segs_low as Hsegs;
  destruct (rt7bd_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
    as (Hin4 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp);
  pose proof HJ as (HAR & _);
  pose proof (rt7bd_T_entry W memc regs F R d _ HF32 HF0 ltac:(unfold RT7BD_HI; lia) HFR HR1 HFp Hval Hd
    H20 H23 H18 H9 H12 H16 H11 H17 H5 H7 H28 H21) as HS;
  pose proof (rt7bd_shok B lyc Sc W memc mdc regs (rt7bd_extra d) (mrestrict (w_H W) memc) F pos HAR Hin4 HF H20 H23
    H18 ltac:(lia) ltac:(lia)) as SHOK;
  assert (X20 : ew (Ereg regs (rt7bd_extra d)) 20 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20);
  assert (X23 : ew (Ereg regs (rt7bd_extra d)) 23 = Z_to_bv 64 (F + 0xe0))
    by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23);
  assert (X18 : ew (Ereg regs (rt7bd_extra d)) 18 = Z_to_bv 64 (F + 0xa0))
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18);
  assert (U23 : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 23) = F + 0xe0)
    by (rewrite X23; apply unsigned_lit_small; lia);
  assert (U18 : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 18) = F + 0xa0)
    by (rewrite X18; apply unsigned_lit_small; lia);
  assert (U23F : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 23) = frame_addr lyc 4 pos + 0xe0)
    by (rewrite U23, HF; reflexivity);
  assert (U18F : bv_unsigned (ew (Ereg regs (rt7bd_extra d)) 18) = frame_addr lyc 4 pos + 0xa0)
    by (rewrite U18, HF; reflexivity);
  assert (HAE : env_agree 32 (Ereg regs (rt7bd_extra d)) (Ereg regs (rt7bd_extra d))) by apply env_agree_refl;
  unfold cfg_at; change (w64 RT7BD_LOOP) with (Z_to_bv 64 RT7BD_LOOP);
  aj_run_to_tok rt7b_tbl_ok HS HJ SHOK RT7BD_Bspan RT7BD_P2;
  [ ..
  | rt7bd_awr U23F U18F Hown
  | rt7bd_leaf B regs W memc F d U23 U18 HAE H5 H7 H28 H21 ];
  rt7bd_obl F X20 X23 Hfsh HF8.

Print Assumptions rt7bd_lit1_ok.
Print Assumptions rt7bd_pins_ok.
Print Assumptions rt7bd_lnot_range.
Print Assumptions rt7bd_bytes_of.
Print Assumptions rt7bd_frame.
Print Assumptions rt7bd_shok.
Print Assumptions rt7bd_T_entry.
