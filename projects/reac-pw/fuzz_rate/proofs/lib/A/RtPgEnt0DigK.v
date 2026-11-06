(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module names changed; 243 of its 274 lines of code are new or changed and 259 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the kit of the DIG block of
   ent_build's case 0 (pod.h:237-246, c < 200), the walk from lib/A/RtPgEnt0Def.v rt7_cut_DIG at 0x813f8 to G =
   0x8150c. Proves no function (kind: segment lemma).

   THE CODE AND ITS THREE RUNS. A run that stores a shadow byte is a plain engine run with the frame's shadow byte
   writable; a run that passes an instrumented check is a token run (lib/Reusable/YCbn.v) with no shadow byte in its
   regions and r and ch listed in the shadow entries rt7d_SH. So the block is three runs:
     P1  0x813f8 .. 0x81408  plain: a3 := 0, a4 := c & 0x3f, `sb 4,0x1c(s4)` (r's granule, shadow_addr F + 28,
                             := 0x04), a6 := 1
     T   0x8140c .. 0x81500  token: the digits loop (r[k] := '0' + v mod 10 at s3 + k with its store check, slow
                             block 0x81460; v / 10 by `mulhu` with t2 and `srli 0x23`; `bltu t0,a5` with t0 = 9),
                             the reverse copy ch[i] := r[k-1-i] (s6 + i; the load check of r, slow block 0x814cc,
                             the store check of ch, slow block 0x814d8) and the NUL ch[k] := 0 (slow block 0x8212c)
     P2  0x81504 .. 0x81508  plain: `sb -8,0x1c(s4)` (r out of scope)
   The token run takes v = c mod 64 as a literal (one engine run per v < 64, lib/A/RtPgEnt0DigT0.v .. T3.v): then
   every branch is decided and every byte of r and ch is a literal chunk. Its obligations are the one-byte checks of
   r and ch, paid by lib/A/RtPgMem.v rtm_A_ra_r / rtm_A_ra_ch from the frame's shadow row rt7_PR.
   THE ENGINE STATES. Atom 18 = s2 = K is the token's shadow base (RtPgW7bBase W7Bx); atom 19 = s3 = F + 0xe0
   bases r's 4 bytes, atom 22 = s6 = F + 0xa0 bases ch's 24; both are 32-aligned (the frame for locals is a
   class-3 side-stack frame, F mod 32 = 0). The plain runs' one region is shadow_addr F + 28, based at atom 20 = s4. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW7bBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgEnt0Def.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition RT7D_P1 : Z := 0x813f8.     (* = RT7_DIG *)
Definition RT7D_LOOP : Z := 0x8140c.   (* the digits loop's head *)
Definition RT7D_P2 : Z := 0x81504.     (* after the NUL store: `addi a0,zero,-8` *)
Definition RT7D_G : Z := 0x8150c.      (* = RS_G *)
Lemma rt7d_pcs : RT7D_P1 = RT7_DIG /\ RT7D_G = RS_G.
Proof. split; reflexivity. Qed.

(* ======================================== the engine states ======================================== *)
(* the plain runs: the frame's shadow byte of r's granule, based at s4 = shadow_addr F *)
Definition rt7d_rRow : YP09.region := YP09.mkRegion (Some 20%nat) 0x1c 0x1d 0x1c 0x1d [].
Definition rt7d_ssP (pc : Z) : sstate := mkSS pc sr_atoms [rt7d_rRow] None (mkFacts [] [] []).
(* the token run: r[4] at s3 = F + 0xe0, ch[24] at s6 = F + 0xa0, both writable; s2 = K exactly *)
Definition rt7d_rR : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 4 [].
Definition rt7d_rCh : YP09.region := YP09.mkRegion (Some 22%nat) 0 24 0 24 [].
Definition RT7D_HI : Z := 2 ^ 47 - 16384.
Definition rt7d_fT : facts :=
mkFacts [(18%nat, mkAF W7SB W7SB 0); (19%nat, mkAF 4096 RT7D_HI 5); (22%nat, mkAF 4096 RT7D_HI 5)] [] [].
Definition rt7d_SH : list shent := [mkSHE 19 4 0; mkSHE 22 24 0].
Definition rt7d_ss0 : sstate := mkSS RT7D_LOOP sr_atoms [rt7d_rR; rt7d_rCh] None rt7d_fT.
(* the loop's six values: a3 = 0, a4 = v, a6 = 1, a7 = 10, t0 = 9, t2 = the `v / 10` multiplier *)
Definition rt7d_ssT (v : Z) : sstate :=
mkSS RT7D_LOOP
  (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 13%bv (SLit 0)) 14%bv (SLit v)) 16%bv (SLit 1))
     17%bv (SLit 10)) 5%bv (SLit 9)) 7%bv (SLit RS_MULT10))
  [rt7d_rR; rt7d_rCh] None rt7d_fT.

(* the registers the token run changes (a0 .. a7, the three slow blocks' scratch included) and t0, t2 (pinned) *)
Definition rt7d_clobT : list (bv 5) := [5; 7; 10; 11; 12; 13; 14; 15; 16; 17]%bv.
(* the bytes it writes: r and ch *)
Definition rt7d_wT (F : Z) : Z -> Prop := fun a => F + 0xe0 <= a < F + 0xe4 \/ F + 0xa0 <= a < F + 0xb8.
(* the byte the plain runs write *)
Definition rt7d_wP (F : Z) : Z -> Prop := fun a => a = shadow_addr F + 28.

(* ======================================== reading a region back ======================================== *)
(* a one-byte literal chunk at offset o holding z *)
Definition rt7d_lit1 (c : YP09.chunk) (o z : Z) : bool :=
match c with
| YP09.mkChunk o' (CVal w (SLit z')) => (w =? 1)%N && (o' =? o) && (z' =? z)
| _ => false
end.
(* region i is based at atom n and holds the bytes l from its offset 0 on, each as a one-byte literal chunk *)
Definition rt7d_bytes_chk (ss : sstate) (i n : nat) (l : list byte) : bool :=
match nth_error (ss_mem ss) i with
| Some r =>
    match YP09.r_base r with
    | Some n' => Nat.eqb n' n &&
        forallb (fun j => existsb (fun c => rt7d_lit1 c (Z.of_nat j) (bv_unsigned (nth j l (Z_to_bv 8 0))))
                   (YP09.r_chunks r)) (seq 0 (length l))
    | None => false
    end
| None => false
end.

Lemma rt7d_lit1_ok : forall c o z, rt7d_lit1 c o z = true -> c = YP09.mkChunk o (CVal 1 (SLit z)).
Proof.
intros [o' cv] o z H. unfold rt7d_lit1 in H.
destruct cv as [w e | len | len | d s len]; cbv beta iota in H; try discriminate H.
destruct e as [z' | | | | | | | | | |]; cbv beta iota in H; try discriminate H.
apply andb_prop in H as [H Hz]. apply andb_prop in H as [Hw Ho].
apply N.eqb_eq in Hw. apply Z.eqb_eq in Ho. apply Z.eqb_eq in Hz. subst. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma rt7d_bytes_of : forall E ss (H : word -> bool) ms i n b (l : list byte),
st_ok rsegs E ss (restrict H ms) -> bv_unsigned (ew E n) = b -> rt7d_bytes_chk ss i n l = true ->
rtm_bytes rsegs H (ms_mem ms) b l.
Proof.
intros E ss H ms i n b l HS Hb Hc. unfold rt7d_bytes_chk in Hc.
destruct (nth_error (ss_mem ss) i) as [r|] eqn:Hi; [|discriminate].
destruct r as [rb lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_chunks] in Hc.
destruct rb as [n'|]; [|discriminate].
apply andb_prop in Hc as [Hn Hc]. apply Nat.eqb_eq in Hn. subst n'.
pose proof (w7_region_nth E ss (restrict H ms) i _ HS Hi) as Hr.
apply (rtm_bytes_aview rsegs). intros j Hj.
rewrite forallb_forall in Hc. specialize (Hc j ltac:(apply in_seq; lia)).
apply existsb_exists in Hc as (c & Hin & Hl).
apply rt7d_lit1_ok in Hl. subst c.
set (x := nth j l (Z_to_bv 8 0)).
pose proof (bv_unsigned_in_range 8 x) as Hx. change (bv_modulus 8) with 256 in Hx.
pose proof (w7_field E _ n b cs lo hi wlo whi (Z.of_nat j) 1 (SLit (bv_unsigned x)) (bv_unsigned x) Hr Hb Hin
  eq_refl ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(cbn; lia)) as Hv.
exact (rtm_val1_aview rsegs H (ms_mem ms) (b + Z.of_nat j) (bv_unsigned x) Hv Hx).
Qed.

(* a register pinned to a literal it holds *)
Lemma rt7d_pin : forall E ss ms (r : bv 5) z,
st_ok rsegs E ss ms -> bv_eqb r 0 = false -> getr (ms_regs ms) r = Z_to_bv 64 z ->
st_ok rsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof. exact (st_ok_pin_lit rsegs). Qed.

Section d.
Variable B : asyms.

(* ---- the frame for locals at a block's start ---- *)
Lemma rt7d_frame : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (3, pos) own -> F = frame_addr lyc 3 pos ->
In (3, pos) (frames Sc) /\ F mod 32 = 0 /\ F mod 8 = 0 /\ 4096 <= F /\ F + 512 <= alloc_ceiling /\
alloc_ceiling <= 0x7fffff800000 /\
0 <= shadow_addr F /\ shadow_addr F + 64 <= alloc_ceiling /\ (F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F) /\
(forall i, 0 <= i < 64 -> apresent (w_H W) memc (shadow_addr F + i)) /\
(forall a, F <= a < F + 512 -> apresent (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k F pos HJ Hown HF.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF32 & HFapp & HFob & HFsh).
rewrite <- HF in HF32, HFapp, HFob, HFsh. change (fs_frame_bytes 3) with 512 in HFapp, HFob, HFsh.
change (512 / 8) with 64 in HFsh.
destruct (rts_fbounds F HF32 HFapp) as (B0 & B1 & B2 & B3 & B4 & _).
pose proof asan_consts as (C1 & _).
assert (HF8 : F mod 8 = 0).
{ destruct (rts_fdiv F HF32) as [E1 _]. rewrite E1. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring.
  apply Z_mod_mult. }
split; [exact Hin3|]. split; [exact HF32|]. split; [exact HF8|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B4|].
split; [intros i Hi; exact (proj1 (HFsh i Hi))|].
intros a Ha. exact (proj1 (HFob a Ha)).
Qed.

(* ---- the shadow entries of the token run ---- *)
Lemma rt7d_shok : forall lyc Sc W memc mdc (regs : bvmap 5 word) M F pos,
AR rsegs B lyc Sc W memc mdc -> In (3, pos) (frames Sc) -> F = frame_addr lyc 3 pos ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 19 = w64 (F + 0xe0) -> getr regs 22 = w64 (F + 0xa0) ->
0 <= F -> F + 512 < 2 ^ 64 ->
sh_ok rsegs W7Bx rt7d_SH (Ereg regs []) M.
Proof.
intros lyc Sc W memc mdc regs M F pos HAR Hin HF H18 H19 H22 HF0 HF1.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (U18 : U (Ereg regs []) W7Bx = SHADOW_OFF).
{ unfold W7Bx. apply U_atom; [rewrite (ew_Ereg_nat regs [] 18 18%bv eq_refl); exact H18 | exact shadow_off_range]. }
assert (U19 : U (Ereg regs []) (SOff 19 0) = F + 0xe0).
{ apply U_atom; [rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact H19 | lia]. }
assert (U22 : U (Ereg regs []) (SOff 22 0) = F + 0xa0).
{ apply U_atom; [rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl); exact H22 | lia]. }
constructor; [|constructor; [|constructor]].
- refine (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc _ W7Bx 19 (F + 0xe0) 3 pos 0 4 M HAR Hin U18 U19 _ _ _);
    rewrite <- ?HF; change (fs_frame_bytes 3) with 512; lia.
- refine (shent_app_of_frame rsegs B LAWS lyc Sc W memc mdc _ W7Bx 22 (F + 0xa0) 3 pos 0 24 M HAR Hin U18 U22 _ _ _);
    rewrite <- ?HF; change (fs_frame_bytes 3) with 512; lia.
Qed.

(* ---- the entry state of the token run ---- *)
Lemma rt7d_T_entry : forall (W : world rsegs) memc (regs : bvmap 5 word) F v,
F mod 32 = 0 -> 4096 <= F -> F + 512 <= RT7D_HI ->
(forall a, F <= a < F + 512 -> apresent (w_H W) memc a) ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 19 = w64 (F + 0xe0) -> getr regs 22 = w64 (F + 0xa0) ->
getr regs 13 = w64 0 -> getr regs 14 = w64 v -> getr regs 16 = w64 1 -> getr regs 17 = w64 10 ->
getr regs 5 = w64 9 -> getr regs 7 = w64 RS_MULT10 ->
st_ok rsegs (Ereg regs []) (rt7d_ssT v) (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7D_LOOP) memc (seg_rom rsegs))).
Proof.
intros W memc regs F v HF32 HF0 HF1 HFp H18 H19 H22 H13 H14 H16 H17 H5 H7. unfold RT7D_HI in HF1.
assert (HFa : (F + 0xa0) mod 32 = 0).
{ rewrite Z.add_mod by lia. rewrite HF32. reflexivity. }
assert (HFe : (F + 0xe0) mod 32 = 0).
{ rewrite Z.add_mod by lia. rewrite HF32. reflexivity. }
assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = F + 0xe0).
{ rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (U22 : bv_unsigned (ew (Ereg regs []) 22) = F + 0xa0).
{ rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl), H22. unfold w64. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew (Ereg regs []) 18) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs [] 18 18%bv eq_refl), H18. unfold w64. apply unsigned_lit_small.
  exact shadow_off_range. }
assert (HS0 : st_ok rsegs (Ereg regs []) rt7d_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RT7D_LOOP) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (rtm_rw_region rsegs _ _ _ 19%nat (F + 0xe0)); [exact U19 | lia | lia | | constructor].
      intros o Ho. apply HFp. lia.
    + apply (rtm_rw_region rsegs _ _ _ 22%nat (F + 0xa0)); [exact U22 | lia | lia | | constructor].
      intros o Ho. apply HFp. lia.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [rt7d_rR rt7d_rCh YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U22.
    split; [split; [lia | exact I] | split; exact I].
  - split; [|split; exact I]. cbn [rt7d_ss0 rt7d_fT f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U19, U22. unfold W7SB, SHADOW_OFF, RT7D_HI. change (2 ^ 0) with 1. change (2 ^ 5) with 32.
    rewrite Z.mod_1_r, HFa, HFe. repeat split; lia. }
pose proof (rt7d_pin _ _ _ 13%bv 0 HS0 eq_refl H13) as HS1. clear HS0.
pose proof (rt7d_pin _ _ _ 14%bv v HS1 eq_refl H14) as HS2. clear HS1.
pose proof (rt7d_pin _ _ _ 16%bv 1 HS2 eq_refl H16) as HS3. clear HS2.
pose proof (rt7d_pin _ _ _ 17%bv 10 HS3 eq_refl H17) as HS4. clear HS3.
pose proof (rt7d_pin _ _ _ 5%bv 9 HS4 eq_refl H5) as HS5. clear HS4.
pose proof (rt7d_pin _ _ _ 7%bv RS_MULT10 HS5 eq_refl H7) as HS6. clear HS5.
exact HS6.
Qed.

(* ---- the block statement of the token run, for one value v of c mod 64 ---- *)
Definition rt7d_T_stmt (v : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (F pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
In (3, pos) own -> F = frame_addr lyc 3 pos ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 19 = w64 (F + 0xe0) -> getr regs 22 = w64 (F + 0xa0) ->
getr regs 13 = w64 0 -> getr regs 14 = w64 v -> getr regs 16 = w64 1 -> getr regs 17 = w64 10 ->
getr regs 5 = w64 9 -> getr regs 7 = w64 RS_MULT10 ->
rt_fsh rsegs (w_H W) memc F rt7_PR ->
SRr rsegs W (cfg_at rsegs RT7D_LOOP regs memc mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7D_P2 regs memc mdc rt7d_clobT (rt7d_wT F)
 (fun _ mem2 => rtm_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 v ++ [Cursor.NUL]))).
End d.
End b.

(* ======================================== the tactic of one token run ======================================== *)
(* one obligation: the one-byte check of r[j] or ch[j], from the row rt7_PR *)
Ltac rt7d_obl F X18 X19 X22 Hfsh HF8 :=
  cbn [ms_mem mkst]; unfold W7Bx;
  change (rd_of rsegs (mrestrict ?H ?m)) with (aview rsegs H m);
  rewrite (U_atom _ 18 SHADOW_OFF X18 shadow_off_range);
  lazymatch goal with
  | |- range_addressable _ _ (U _ (SOff 19 ?j)) _ =>
      rewrite (U_atom_off _ 19 (F + 0xe0) j X19 ltac:(lia) ltac:(lia));
      replace (F + 0xe0 + j) with (F + RTM_R + j) by (unfold RTM_R; lia);
      apply (rtm_A_ra_r rsegs _ _ F true true true false false false j 1 Hfsh HF8); lia
  | |- range_addressable _ _ (U _ (SOff 22 ?j)) _ =>
      rewrite (U_atom_off _ 22 (F + 0xa0) j X22 ltac:(lia) ltac:(lia));
      replace (F + 0xa0 + j) with (F + RTM_CH + j) by (unfold RTM_CH; lia);
      apply (rtm_A_ra_ch rsegs _ _ F true true true false false false j 1 Hfsh HF8); lia
  end.
(* the write rights of r and ch: the frame for locals' own bytes *)
Ltac rt7d_awr U19F U22F Hown :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 19%nat _ 0xe0); [reflexivity | exact U19F | exact Hown | cbn; lia | cbn; lia |];
  eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 22%nat _ 0xa0); [reflexivity | exact U22F | exact Hown | cbn; lia | cbn; lia |];
  apply awr_ok_nil.
(* the leaf: the journal, the I/O state, the registers outside rt7d_clobT, the bytes outside r and ch, ch's text *)
Ltac rt7d_post B regs W memc F U19 U22 HAE :=
  lazymatch goal with
  | HS : st_ok _ ?E' ?ssf (restrict (w_H W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFr : frame_of _ _ (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ?ms)),
    HG : mem_grows _ _ |- _ =>
    assert (HA : env_agree 32 (Ereg regs []) E') by env_agree_chain HAE;
    eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ];
    [ eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [exact HA | vm_compute; reflexivity]
    | let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
      intros a Ha Hz;
      refine (w7_kept_run (rt7d_wT F) _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr _ a Ha Hz);
      let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros x (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      repeat (destruct Hin as [<-|Hin];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U19, ?U22 in Hr; unfold rt7d_wT; lia |]);
      destruct Hin
    | cbv beta;
      apply (rt7d_bytes_of E' ssf (w_H W) ms 1 22 (F + 0xa0));
      [ exact HS | rewrite (proj1 HA 22%nat ltac:(lia)); exact U22 | vm_compute; reflexivity ] ]
  end.
Ltac rt7d_T_tac :=
  let B := lazymatch goal with |- rt7d_T_stmt ?B _ => B end in
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F pos HJ Hown HF H18 H19 H22 H13 H14 H16 H17
    H5 H7 Hfsh;
  pose proof (AR_laws_ok rsegs B) as LAWS;
  pose proof w7_wx as Hwx; pose proof w7_segs_low as Hsegs;
  destruct (rt7d_frame B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hown HF)
    as (Hin3 & HF32 & HF8 & HF0 & HFc & Hceil & HS0 & HS1 & HSd & HFsh & HFp);
  pose proof HJ as (HAR & _);
  pose proof (rt7d_T_entry W memc regs F _ HF32 HF0 ltac:(unfold RT7D_HI; lia) HFp H18 H19 H22 H13 H14 H16
    H17 H5 H7) as HS;
  pose proof (rt7d_shok B lyc Sc W memc mdc regs (mrestrict (w_H W) memc) F pos HAR Hin3 HF H18 H19 H22
    ltac:(lia) ltac:(lia)) as SHOK;
  assert (X18 : ew (Ereg regs []) 18 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs [] 18 18%bv eq_refl); exact H18);
  assert (X19 : ew (Ereg regs []) 19 = Z_to_bv 64 (F + 0xe0))
    by (rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact H19);
  assert (X22 : ew (Ereg regs []) 22 = Z_to_bv 64 (F + 0xa0))
    by (rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl); exact H22);
  assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = F + 0xe0)
    by (rewrite X19; apply unsigned_lit_small; lia);
  assert (U22 : bv_unsigned (ew (Ereg regs []) 22) = F + 0xa0)
    by (rewrite X22; apply unsigned_lit_small; lia);
  assert (U19F : bv_unsigned (ew (Ereg regs []) 19) = frame_addr lyc 3 pos + 0xe0) by (rewrite U19, HF; reflexivity);
  assert (U22F : bv_unsigned (ew (Ereg regs []) 22) = frame_addr lyc 3 pos + 0xa0) by (rewrite U22, HF; reflexivity);
  assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl;
  unfold cfg_at; change (w64 RT7D_LOOP) with (Z_to_bv 64 RT7D_LOOP);
  aj_run_to_tok rt7_tbl_ok HS HJ SHOK W7Bspan RT7D_P2;
  [ ..
  | rt7d_awr U19F U22F Hown
  | rt7d_post B regs W memc F U19 U22 HAE ];
  rt7d_obl F X18 X19 X22 Hfsh HF8.
