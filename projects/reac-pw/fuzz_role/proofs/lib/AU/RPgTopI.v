(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgTopI.v at ad0e022f7af for image B, in the
   form of proofs/reac-pw/fuzz_rate/lib/AU/RtPgTopIB.v at 2e01bfcb541: image B's segments (lib/AU/Img0.v), its
   read-only range (.data.rel.ro start 0x9a3c0 .. .got end 0x9b7c8), the segment statements of lib/AU/RPgHarn.v, the
   pieces of lib/AU/RPgSeg.v, the chaining of lib/AU/RPgTop.v and the two middle contracts closed by
   lib/AU/RPgMainL.v. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses from the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): THE WHOLE RUN OF LLVMFuzzerTestOneInput AT IMAGE
   B's SEGMENTS (lib/AU/Img0.v rsegs = images.AsanUbsan.M.loaded_segments, the relocated frame's YB1v.tfibsegs) and
   its read-only range 0x9a3c0 .. 0x9b7c8 (RPgLib.RO_LO / RO_HI: .data.rel.ro start .. .got end, from the section
   headers of the pinned file: .data.rel.ro 0x9a3c0 .. 0x9aa70, .got 0x9aa70 .. 0x9b7c8), for every symbol record B
   whose static facts hold (RPgHarn.rh_static_law).

     role_lib_x_B : rl_lib_contract_x Img0.rsegs B ameter_triv K XL XL 0x9a3c0 0x9b7c8 A_LLVMF RA_LLVMF ...

   It instantiates lib/AU/RPgTop.v role_lib_x and discharges what does not belong to a walk piece:
   - the read-only range lies in the image (one loaded segment holds .data.rel.ro and .got) and, with every
     non-writable segment, below the sink's overflow head when that head is at or above 0x9b7c8 (HOFL);
   - role_build_contract by RPgMainL.role_build_holds over the build's pieces, role_check_contract by
     RPgMainL.role_check_holds over the checks' pieces.
   What remains are the walk pieces' statements (each the exact rs_piece_*_stmt of lib/AU/RPgSeg.v or S_E01 / S_X01 /
   rh_S_C23_stmt of lib/AU/RPgHarn.v at Img0.rsegs and the trivial meter), the static law of the symbols, the
   harness constants' three numeric facts, the sink's laws and the lib shape's leaf law. Proves no function of its
   own (kind: merge). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgMainL RPgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The read-only range 0x9a3c0 .. 0x9b7c8 lies in one loaded segment (the RW PT_LOAD of .data.rel.ro and .got). *)
Lemma role_relro_B_chk : existsb (fun s => (Z.of_N (seg_base s) <=? 0x9a3c0) &&
  (0x9b7c8 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* Every non-writable loaded segment ends at or below 0x9b7c8. *)
Lemma role_rom_end_B_chk : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x9b7c8))
  rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.

Lemma role_relro_B : forall a, 0x9a3c0 <= a < 0x9b7c8 -> in_img rsegs a.
Proof.
pose proof role_relro_B_chk as C. apply existsb_exists in C as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
intros a Ha. exists s. split; [exact Hs | lia].
Qed.

(* the sink's overflow head of the relocated frame (YE2k.tfib_sink_head) lies above the read-only data *)
Hypothesis HOFL : 0x9b7c8 <= YI16.sk_ofl_head.
#[local] Instance role_ro_B : ro_below_ofl rsegs 0x9a3c0 0x9b7c8.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|lia].
pose proof role_rom_end_B_chk as C. rewrite forallb_forall in C. pose proof (C s Hs) as Cs.
rewrite Hw in Cs. cbn [orb] in Cs. apply Z.leb_le in Cs. lia.
Qed.

Variable B : asyms.
(* the static facts of the symbols (the start-up's const cells, zero-shadow ranges and pinned owned bytes) *)
Hypothesis HSTAT : rh_static_law rsegs B 0x9a3c0 0x9b7c8.
Variable K : asink_syms.
Variable XL : Z -> Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness constants (the relocated frame's YCfn: A_LLVMF 0x80020, EV_LIB, LLVMF_STK; by computation) *)
Hypothesis HA : A_LLVMF = RH_ENTRY.
Hypothesis HEV : RH_EV <= EV_LIB.
Hypothesis HSTK : RH_RSZ + 32 + ASTACK <= LLVMF_STK.
(* the core's sink laws at the symbols (the relocated frame's YD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws rsegs B K.
(* the lib shape's one-leaf law (role_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).

(* ---------------- the walk pieces' statements at image B ---------------- *)
(* S_E01: ENTRY -> C1 *)
Hypothesis HE01 : S_E01 rsegs B 0x9a3c0 0x9b7c8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* C2 -> C3 (malloc(pod)) *)
Hypothesis HC23 : rh_S_C23_stmt rsegs B 0x9a3c0 0x9b7c8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* S_X01: C4 -> the return *)
Hypothesis HX01 : S_X01 rsegs B 0x9a3c0 0x9b7c8 RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
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

Theorem role_lib_x_B : rl_lib_contract_x rsegs B ameter_triv K XL XL 0x9a3c0 0x9b7c8
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
eapply (role_lib_x rsegs B).
all: first
  [ exact role_relro_B
  | exact role_ro_B
  | exact HSTAT
  | (apply role_build_holds; assumption)
  | (apply role_check_holds; assumption)
  | eassumption ].
Qed.
End i.
