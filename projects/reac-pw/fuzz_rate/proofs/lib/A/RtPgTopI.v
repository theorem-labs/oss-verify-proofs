(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgTopI.v at ad0e022f7af7 for reac-pw/fuzz_rate
   image A: rate's read-only range (.data.rel.ro start 0x9b6e0 .. .got end 0x9cb68), rate's five segment statements
   (lib/A/RtPgSeg.v S_E01 .. S_X01 and the two malloc steps) and rate's three middle contracts closed from their
   pieces by lib/A/RtPgMainL.v. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses from the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): THE WHOLE RUN OF LLVMFuzzerTestOneInput AT IMAGE
   A's SEGMENTS (lib/A/Img0.v rsegs = images.Asan.M.loaded_segments, the relocated frame's AB1v.tfibsegs) and its
   read-only range 0x9b6e0 .. 0x9cb68 (RtPgLib.RO_LO / RO_HI: .data.rel.ro start .. .got end, from the section headers
   of the pinned file), for every symbol record B whose static facts hold (RtPgSeg.rh_static_law).

     rate_lib_x_A : rt_lib_contract_x Img0.rsegs B ameter_triv K XL XL 0x9b6e0 0x9cb68 A_LLVMF RA_LLVMF ...

   It instantiates lib/A/RtPgTop.v rate_lib_x and discharges what does not belong to a walk piece:
   - the read-only range lies in the image (the RW PT_LOAD [0x9b690, 0x9d000) that holds .data.rel.ro and .got) and,
     with every non-writable segment, below the sink's overflow head when that head is at or above 0x9cb68 (HOFL);
   - rate_build_contract by RtPgMainL.rate_build_holds over the build's pieces, rate_check_contract by
     RtPgMainL.rate_check_holds over the checks' pieces, rate_csv_contract (at every float state) by
     RtPgMainL.rate_csv_holds over the list's piece.
   What remains are the walk pieces' statements (each the exact rs_piece_*_stmt, S_E01 / S_X01 or rh_S_C23_stmt /
   rh_S_C46_stmt of lib/A/RtPgSeg.v at Img0.rsegs and the trivial meter), the static law of the symbols (the start-up's
   const cells and zero-shadow ranges), the harness constants' three numeric facts, the sink's laws and the lib shape's
   leaf law; the relocated frame's RtPgLib.rate_lib_x_all_stmt is this theorem at AD2l.TfibB, AE2k.tfib_K and ACfn's
   constants. Proves no function of its own (kind: merge). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec RtPgImgA RtPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgMainL RtPgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The read-only range 0x9b6e0 .. 0x9cb68 lies in one loaded segment (the RW PT_LOAD of .data.rel.ro and .got). *)
Lemma rate_relro_A_chk : existsb (fun s => (Z.of_N (seg_base s) <=? 0x9b6e0) &&
  (0x9cb68 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* Every non-writable loaded segment ends at or below 0x9cb68. *)
Lemma rate_rom_end_chk : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x9cb68))
  rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.

Lemma rate_relro_A : forall a, 0x9b6e0 <= a < 0x9cb68 -> in_img rsegs a.
Proof.
pose proof rate_relro_A_chk as C. apply existsb_exists in C as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
intros a Ha. exists s. split; [exact Hs | lia].
Qed.

(* the sink's overflow head of the relocated frame (AE2k.tfib_sink_head) lies above the read-only data *)
Hypothesis HOFL : 0x9cb68 <= YI16.sk_ofl_head.
#[local] Instance rate_ro_A : ro_below_ofl rsegs 0x9b6e0 0x9cb68.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|lia].
pose proof rate_rom_end_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Variable B : asyms.
(* the static facts of the symbols (the start-up's const cells, zero-shadow ranges and pinned owned bytes) *)
Hypothesis HSTAT : rh_static_law rsegs B 0x9b6e0 0x9cb68.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants (the relocated frame's ACfn: A_LLVMF 0x80714, EV_LIB, LLVMF_STK; by computation) *)
Hypothesis HA : A_LLVMF = RS_ENTRY.
Hypothesis HEV : RS_EV <= EV_LIB.
Hypothesis HSTK : RS_RSZ + 32 + ASTACK <= LLVMF_STK.
(* the core's sink laws at the symbols (the relocated frame's AD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law (RtPgLib.rate_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* ---------------- the walk pieces' statements at image A ---------------- *)
(* S_E01: ENTRY -> C1 *)
Hypothesis HE01 : S_E01 rsegs B 0x9b6e0 0x9cb68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* C2 -> C3 (malloc(pod)) *)
Hypothesis HC23 : rh_S_C23_stmt rsegs B 0x9b6e0 0x9cb68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* C4 -> C6 (malloc(buf)) *)
Hypothesis HC46 : rh_S_C46_stmt rsegs B 0x9b6e0 0x9cb68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* S_X01: C7 -> the return *)
Hypothesis HX01 : S_X01 rsegs B 0x9b6e0 0x9cb68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* the build's pieces (in RtPgSeg.v's order) *)
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
Hypothesis PW13 : rs_piece_W13_stmt rsegs B ameter_triv.
Hypothesis PW14_asked : rs_piece_W14_asked_stmt rsegs B ameter_triv.
Hypothesis PW14_tail : rs_piece_W14_tail_stmt rsegs B ameter_triv.
(* the list's piece, at every float state (the list runs at the float state the checks return at) *)
Hypothesis PW14_csv : forall fx' : YK11.FPState, @rs_piece_W14_csv_stmt fx' rc SK rsegs B ameter_triv.

Theorem rate_lib_x_A : rt_lib_contract_x rsegs B ameter_triv K XL XL 0x9b6e0 0x9cb68
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (rate_lib_x rsegs B).
all: first
  [ exact rate_relro_A
  | exact rate_ro_A
  | exact HSTAT
  | (apply rate_build_holds; assumption)
  | (apply rate_check_holds; assumption)
  | (intros fx'; apply rate_csv_holds; exact (PW14_csv fx'))
  | eassumption ].
Qed.
End i.

Print Assumptions rate_lib_x_A.
