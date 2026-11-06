(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgTopI.v at ad0e022f7af7 for reac-pw/fuzz_rate
   image A: rate's read-only range (.data.rel.ro start 0x9b6e0 .. .got end 0x9cb68), rate's five segment statements
   (lib/A/RtPgSeg.v S_E01 .. S_X01 and the two malloc steps) and rate's three middle contracts closed from their
   pieces by lib/A/RtPgMainL.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgTopI.v at af0538adbf24 for image B
   (fuzz_rate.asan-ubsan): image B's segments (lib/AU/Img0.v), its read-only range (.data.rel.ro start 0x9b9e0 ..
   .got end 0x9ce68), the segment statements and pieces of lib/AU/RtPgSegB.v, the chaining of lib/AU/RtPgTopB.v and
   the three middle contracts closed by lib/AU/RtPgMainLB.v. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): THE WHOLE RUN OF LLVMFuzzerTestOneInput AT IMAGE
   B's SEGMENTS (lib/AU/Img0.v rsegs = images.AsanUbsan.M.loaded_segments) and its read-only range 0x9b9e0 .. 0x9ce68
   (.data.rel.ro start .. .got end, from the section headers of the pinned file: .data.rel.ro 0x9b9e0 .. 0x9c110,
   .got 0x9c110 .. 0x9ce68, both in the RW PT_LOAD [0x9b998, 0x9d000); the same in the unstripped twin), for every
   symbol record B whose static facts hold (RtPgSegB.rhb_static_law).

     rate_lib_x_B_pieces : rt_lib_contract_x Img0.rsegs B ameter_triv K XL XL 0x9b9e0 0x9ce68 A_LLVMF RA_LLVMF ...

   It instantiates lib/AU/RtPgTopB.v rate_lib_xb and discharges what does not belong to a walk piece:
   - the read-only range lies in the image (the RW PT_LOAD that holds .data.rel.ro and .got) and, with every
     non-writable segment, below the sink's overflow head when that head is at or above 0x9ce68 (HOFL);
   - rate_build_contract by RtPgMainLB.rate_build_holds over the build's pieces, rate_check_contract by
     RtPgMainLB.rate_check_holds over the checks' pieces, rate_csv_contract (at every float state) by
     RtPgMainLB.rate_csv_holds over the list's piece.
   What remains are the walk pieces' statements (each the exact rsb_piece_*_stmt, S_E01 / S_X01 or rhb_S_C23_stmt /
   rhb_S_C46_stmt of lib/AU/RtPgSegB.v at Img0.rsegs and the trivial meter), the static law of the symbols, the
   harness constants' three numeric facts, the sink's laws and the lib shape's leaf law. Proves no function of its own
   (kind: merge). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0 RtPgImgB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMainLB RtPgTopB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The read-only range 0x9b9e0 .. 0x9ce68 lies in one loaded segment (the RW PT_LOAD of .data.rel.ro and .got). *)
Lemma rate_relro_B_chk : existsb (fun s => (Z.of_N (seg_base s) <=? 0x9b9e0) &&
  (0x9ce68 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* Every non-writable loaded segment ends at or below 0x9ce68. *)
Lemma rate_rom_end_B_chk : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x9ce68))
  rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.

Lemma rate_relro_B : forall a, 0x9b9e0 <= a < 0x9ce68 -> in_img rsegs a.
Proof.
pose proof rate_relro_B_chk as C. apply existsb_exists in C as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
intros a Ha. exists s. split; [exact Hs | lia].
Qed.

(* the sink's overflow head lies above the read-only data *)
Hypothesis HOFL : 0x9ce68 <= YI16.sk_ofl_head.
#[local] Instance rate_ro_B : ro_below_ofl rsegs 0x9b9e0 0x9ce68.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|lia].
pose proof rate_rom_end_B_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Variable B : asyms.
(* the static facts of the symbols (the start-up's const cells, zero-shadow ranges and pinned owned bytes) *)
Hypothesis HSTAT : rhb_static_law rsegs B 0x9b9e0 0x9ce68.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants (image B's entry 0x8076c, the event budget, the harness's stack) *)
Hypothesis HA : A_LLVMF = RSB_ENTRY.
Hypothesis HEV : RSB_EV <= EV_LIB.
Hypothesis HSTK : RSB_RSZ + 32 + ASTACK <= LLVMF_STK.
(* the core's sink laws at the symbols *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* ---------------- the walk pieces' statements at image B ---------------- *)
(* S_E01: ENTRY -> C1 *)
Hypothesis HE01 : S_E01 rsegs B 0x9b9e0 0x9ce68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* C2 -> C3 (malloc(pod)) *)
Hypothesis HC23 : rhb_S_C23_stmt rsegs B 0x9b9e0 0x9ce68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* C4 -> C6 (malloc(buf)) *)
Hypothesis HC46 : rhb_S_C46_stmt rsegs B 0x9b9e0 0x9ce68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* S_X01: C7 -> the return *)
Hypothesis HX01 : S_X01 rsegs B 0x9b9e0 0x9ce68 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* the build's pieces (in RtPgSegB.v's order) *)
Hypothesis PW3a : rsb_piece_W3a_stmt rsegs B ameter_triv.
Hypothesis PW3b_hdr : rsb_piece_W3b_hdr_stmt rsegs B ameter_triv.
Hypothesis PW3b_b7 : rsb_piece_W3b_b7_stmt rsegs B ameter_triv.
Hypothesis PW3b_pre : rsb_piece_W3b_pre_stmt rsegs B ameter_triv.
Hypothesis PW4_sel : rsb_piece_W4_sel_stmt rsegs B ameter_triv.
Hypothesis PW4_int7 : rsb_piece_W4_int7_stmt rsegs B ameter_triv.
Hypothesis PW4_key : rsb_piece_W4_key_stmt rsegs B ameter_triv.
Hypothesis PW4_latch : rsb_piece_W4_latch_stmt rsegs B ameter_triv.
Hypothesis PW5_int : rsb_piece_W5_int_stmt rsegs B ameter_triv.
Hypothesis PW5_open : rsb_piece_W5_open_stmt rsegs B ameter_triv.
Hypothesis PW5_close : rsb_piece_W5_close_stmt rsegs B ameter_triv.
Hypothesis PW6a_disp : rsb_piece_W6a_disp_stmt rsegs B ameter_triv.
Hypothesis PW6a_cases : rsb_piece_W6a_cases_stmt rsegs B ameter_triv.
Hypothesis PW6b : rsb_piece_W6b_stmt rsegs B ameter_triv.
Hypothesis PW6c : rsb_piece_W6c_stmt rsegs B ameter_triv.
Hypothesis PW7a : rsb_piece_W7a_stmt rsegs B ameter_triv.
Hypothesis PW7b : rsb_piece_W7b_stmt rsegs B ameter_triv.
Hypothesis PW8 : rsb_piece_W8_stmt rsegs B ameter_triv.
Hypothesis PW10_post : rsb_piece_W10_post_stmt rsegs B ameter_triv.
Hypothesis PW10_corr : rsb_piece_W10_corr_stmt rsegs B ameter_triv.
Hypothesis PW10_req : rsb_piece_W10_req_stmt rsegs B ameter_triv.
(* the checks' pieces *)
Hypothesis PW11a_head : rsb_piece_W11a_head_stmt rsegs B ameter_triv.
Hypothesis PW11a_setup : rsb_piece_W11a_setup_stmt rsegs B ameter_triv.
Hypothesis PW11a_outer : rsb_piece_W11a_outer_stmt rsegs B ameter_triv.
Hypothesis PW11a_inner : rsb_piece_W11a_inner_stmt rsegs B ameter_triv.
Hypothesis PW11b_key : rsb_piece_W11b_key_stmt rsegs B ameter_triv.
Hypothesis PW11b_checks : rsb_piece_W11b_checks_stmt rsegs B ameter_triv.
Hypothesis PW13 : rsb_piece_W13_stmt rsegs B ameter_triv.
Hypothesis PW14_asked : rsb_piece_W14_asked_stmt rsegs B ameter_triv.
Hypothesis PW14_tail : rsb_piece_W14_tail_stmt rsegs B ameter_triv.
(* the list's piece, at every float state (the list runs at the float state the checks return at) *)
Hypothesis PW14_csv : forall fx' : YK11.FPState, @rsb_piece_W14_csv_stmt fx' rc SK rsegs B ameter_triv.

Theorem rate_lib_x_B_pieces : rt_lib_contract_x rsegs B ameter_triv K XL XL 0x9b9e0 0x9ce68
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (rate_lib_xb rsegs B).
all: first
  [ exact rate_relro_B
  | exact rate_ro_B
  | exact HSTAT
  | (apply rate_build_holds; assumption)
  | (apply rate_check_holds; assumption)
  | (intros fx'; apply rate_csv_holds; exact (PW14_csv fx'))
  | eassumption ].
Qed.
End i.

Print Assumptions rate_lib_x_B_pieces.
