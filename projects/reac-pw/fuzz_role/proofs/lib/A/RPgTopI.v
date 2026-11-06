(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses from the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): THE WHOLE RUN OF LLVMFuzzerTestOneInput AT IMAGE
   A's SEGMENTS (lib/A/Img0.v rsegs = images.Asan.M.loaded_segments, the relocated frame's AB1v.tfibsegs) and its
   read-only range 0x9a120 .. 0x9b528 (RPgLib.RO_LO / RO_HI: .data.rel.ro start .. .got end), for every symbol
   record B whose static facts hold (rh_static_law).

     role_lib_x_A : rl_lib_contract_x Img0.rsegs B ameter_triv K XL XL 0x9a120 0x9b528 A_LLVMF RA_LLVMF ...

   It instantiates lib/A/RPgTop.v role_lib_x and discharges what does not belong to a walk lane:
   - rh_static_law is taken as a premise here (HSTAT); lib/A/RPgStatA.v rh_static_A proves it for every B with
     A2's TfibSyms (A2's const cells, zero-shadow ranges and pinned owned bytes);
   - the read-only range lies in the image (the RW PT_LOAD that holds .data.rel.ro and .got) and, with every
     non-writable segment, below the sink's overflow head when that head is at or above 0x9b528 (HOFL);
   - role_build_contract by RPgMainL.role_build_holds over the build pieces, role_check_contract by
     RPgMainL.role_check_holds over the check pieces.
   What remains are the walk lanes' statements (each the exact rs_piece_*_stmt of lib/A/RPgSeg.v or
   rh_S_*_stmt of lib/A/RPgHarn.v at Img0.rsegs and the trivial meter), the harness constants' three numeric
   facts, the sink's laws and the lib shape's leaf law; the relocated frame's RPgLib.role_lib_x_all_stmt is this
   theorem at AD2l.TfibB, AE2k.tfib_K and ACfn's constants. Proves no function of its own (kind: merge). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgMainL RPgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The read-only range 0x9a120 .. 0x9b528 lies in one loaded segment (the RW PT_LOAD of .data.rel.ro and .got). *)
Lemma role_relro_A_chk : existsb (fun s => (Z.of_N (seg_base s) <=? 0x9a120) &&
  (0x9b528 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* Every non-writable loaded segment ends at or below 0x9b528. *)
Lemma role_rom_end_chk : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x9b528))
  rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.

Lemma role_relro_A : forall a, 0x9a120 <= a < 0x9b528 -> in_img rsegs a.
Proof.
pose proof role_relro_A_chk as C. apply existsb_exists in C as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
intros a Ha. exists s. split; [exact Hs | lia].
Qed.

(* the sink's overflow head of the relocated frame (AE2k.tfib_sink_head) lies above the read-only data *)
Hypothesis HOFL : 0x9b528 <= YI16.sk_ofl_head.
#[local] Instance role_ro_A : ro_below_ofl rsegs 0x9a120 0x9b528.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|lia].
pose proof role_rom_end_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Variable B : asyms.
(* the static facts of the symbols (RPgStatA.rh_static_A from A2's TfibSyms) *)
Hypothesis HSTAT : rh_static_law rsegs B 0x9a120 0x9b528.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants (the relocated frame's ACfn: A_LLVMF 0x7ff88, EV_LIB, LLVMF_STK; by computation) *)
Hypothesis HA : A_LLVMF = RH_ENTRY.
Hypothesis HEV : RH_EV <= EV_LIB.
Hypothesis HSTK : RH_RSZ + 32 + ASTACK <= LLVMF_STK.
(* the core's sink laws at the symbols (the relocated frame's AD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law (role_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* ---------------- the walk pieces' statements at image A ---------------- *)
(* S_E01: ENTRY -> C1 *)
Hypothesis HE01 : rh_S_E01_stmt rsegs B 0x9a120 0x9b528 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* C2 -> C3 (malloc(pod)) *)
Hypothesis HC23 : rh_S_C23_stmt rsegs B 0x9a120 0x9b528 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* S_X01: C4 -> the return, at every float state *)
Hypothesis HX01 : forall fx' : YK11.FPState,
  rh_S_X01_stmt (fx := fx') rsegs B 0x9a120 0x9b528 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* the build's pieces (in RPgSeg.v's order) *)
Hypothesis PW3a : rs_piece_W3a_stmt rsegs B ameter_triv.
Hypothesis PW3b_hdr : rs_piece_W3b_hdr_stmt rsegs B ameter_triv.
Hypothesis PW3b_b7 : rs_piece_W3b_b7_stmt rsegs B ameter_triv.
Hypothesis PW3b_pre : rs_piece_W3b_pre_stmt rsegs B ameter_triv.
Hypothesis PW4_sel : rs_piece_W4_sel_stmt rsegs B ameter_triv.
Hypothesis PW4_int7 : rs_piece_W4_int7_stmt rsegs B ameter_triv.
Hypothesis PW4_key : rs_piece_W4_key_stmt rsegs B ameter_triv.
Hypothesis PW4_latch : rs_piece_W4_latch_stmt rsegs B ameter_triv.
Hypothesis PW5_int : rs_piece_W5_int_stmt rsegs B ameter_triv.
Hypothesis PW5_open : rs_piece_W5_open_stmt rsegs B ameter_triv.
Hypothesis PW5_close : rs_piece_W5_close_stmt rsegs B ameter_triv.
Hypothesis PW6a_disp : rs_piece_W6a_disp_stmt rsegs B ameter_triv.
Hypothesis PW6a_cases : rs_piece_W6a_cases_stmt rsegs B ameter_triv.
Hypothesis PW6b : rs_piece_W6b_stmt rsegs B ameter_triv.
Hypothesis PW6c : rs_piece_W6c_stmt rsegs B ameter_triv.
Hypothesis PW7a : rs_piece_W7a_stmt rsegs B ameter_triv.
Hypothesis PW7b : rs_piece_W7b_stmt rsegs B ameter_triv.
Hypothesis PW8 : rs_piece_W8_stmt rsegs B ameter_triv.
Hypothesis PW10_post : rs_piece_W10_post_stmt rsegs B ameter_triv.
Hypothesis PW10_corr : rs_piece_W10_corr_stmt rsegs B ameter_triv.
Hypothesis PW10_req : rs_piece_W10_req_stmt rsegs B ameter_triv.
(* the checks' pieces *)
Hypothesis PW11a_head : rs_piece_W11a_head_stmt rsegs B ameter_triv.
Hypothesis PW11a_setup : rs_piece_W11a_setup_stmt rsegs B ameter_triv.
Hypothesis PW11a_outer : rs_piece_W11a_outer_stmt rsegs B ameter_triv.
Hypothesis PW11a_inner : rs_piece_W11a_inner_stmt rsegs B ameter_triv.
Hypothesis PW11b_key : rs_piece_W11b_key_stmt rsegs B ameter_triv.
Hypothesis PW11b_checks : rs_piece_W11b_checks_stmt rsegs B ameter_triv.
Hypothesis PW11b_tail : rs_piece_W11b_tail_stmt rsegs B ameter_triv.

Theorem role_lib_x_A : rl_lib_contract_x rsegs B ameter_triv K XL XL 0x9a120 0x9b528
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (role_lib_x rsegs B).
all: first
  [ exact role_relro_A
  | exact role_ro_A
  | exact HSTAT
  | (apply role_build_holds; assumption)
  | (apply role_check_holds; assumption)
  | eassumption ].
Qed.
End i.

Print Assumptions role_lib_x_A.
