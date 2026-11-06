(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YG0n YG0t YG0r YG0q YC59 YC6f YCar YC08.
Record rgcx := mkRGCX {
c_ly : alayout; c_S : astate; c_W : world trasegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_ch : list (Z * Z * Z);
c_r : Z; c_cfp : Z; c_g : Z; c_wfn : Z; c_ctx : Z; c_path : Z; c_attr : Z; c_gen : Z; c_loops : Z; c_Wd : Z; c_Hd : Z;
c_bef : Z; c_beffmt : Z; c_cur : Z; c_s : cgif_st; c_N : Z;
c_img : Z; c_fmt : Z; c_fattr : Z; c_fgen : Z; c_delay : Z; c_rest : list (Z * Z);
c_cid : Z; c_pos : Z; c_fpos : Z; c_E0 : env }.
Definition rgc_vals (cx : rgcx) : list Z :=
rga_vals (c_g cx) (c_wfn cx) (c_ctx cx) (c_path cx) (c_attr cx) (c_gen cx) (c_loops cx) (c_Wd cx) (c_Hd cx) (c_bef cx) (c_beffmt cx) (c_cur cx)
(c_img cx) (c_fmt cx) (c_fattr cx) (c_fgen cx) (c_delay cx).
Definition rgc_FP (cx : rgcx) : list (Z * Z) := ablocks_fp (trgb_own (c_r cx) (c_g cx) (c_s cx) (c_N cx) (c_bef cx) (c_beffmt cx)).
Definition rgc_FPs (cx : rgcx) : list (Z * Z) := ablocks_fp [(c_r cx, RGB_SIZE)].
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition rga_base (B : asyms) (cx : rgcx) : Prop :=
afn_pre trasegs B TRGBADD_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) /\
spZ (c_regs cx) mod 32 = 0 /\
In (raZ (c_regs cx) :: spine (c_ch cx)) CTX_cgif_rgb_addframe /\ Z.of_nat (length (frames (c_S cx))) <= 6 /\
spZ (c_regs cx) + 32 <= ly_top (c_ly cx) /\
arodata_ok B (aview trasegs (w_H (c_W cx)) (c_mem cx)) /\
getr (c_regs cx) 10 = w64 (c_r cx) /\ getr (c_regs cx) 11 = w64 (c_cfp cx) /\
(In (c_cid cx, c_pos cx) (frames (c_S cx)) /\ 0 <= c_cid cx /\ frame_addr (c_ly cx) (c_cid cx) (c_pos cx) mod 8 = 0 /\
frame_addr (c_ly cx) (c_cid cx) (c_pos cx) <= c_cfp cx /\ c_cfp cx + 24 <= frame_addr (c_ly cx) (c_cid cx) (c_pos cx) + fs_frame_bytes (c_cid cx) /\
c_cfp cx mod 8 = 0 /\ range_addressable (aview trasegs (w_H (c_W cx)) (c_mem cx)) SHADOW_OFF (c_cfp cx) 24) /\
obj_at trasegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_cfp cx) LAY_RgbFrameConfig [c_img cx; c_fmt cx; c_fattr cx; c_fgen cx; c_delay cx] /\
obj_at trasegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_r cx) LAY_Rgb
[c_g cx; c_wfn cx; c_ctx cx; c_path cx; c_attr cx; c_gen cx; c_loops cx; c_Wd cx; c_Hd cx; c_bef cx; c_beffmt cx; c_cur cx] /\
tcgif_at (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx) (c_s cx) /\ cgif_wf (c_s cx) (c_N cx) /\
cg_W (c_s cx) = c_Wd cx /\ cg_H (c_s cx) = c_Hd cx /\ c_N cx <= RGB_NMAX /\
(c_bef cx = 0 \/ c_beffmt cx = 3 \/ c_beffmt cx = 4) /\
Permutation (ablocks B (c_ly cx) (c_S cx))
(trgb_own (c_r cx) (c_g cx) (c_s cx) (c_N cx) (c_bef cx) (c_beffmt cx) ++ timg_block (c_img cx) (c_fmt cx) (c_N cx) ++ c_rest cx) /\
bud_ok (c_S cx) EV_FRAMEV CN_FRAME WT_FRAME HL_FRAME   /\ blocks_bytes (c_S cx) + LIVE_RGBADD <= LIVE_MAX /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
(forall j, (j < 18)%nat -> ew (c_E0 cx) (32 + j) = Z_to_bv 64 (nth j (rgc_vals cx) 0)) /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx).
Definition rga_F (cx : rgcx) : Z := frame_addr (c_ly cx) 7 (c_fpos cx).
Definition rga_FL (cx : rgcx) : Z := flag_addr (c_ly cx) 7 (c_fpos cx).
Definition rga_E (cx : rgcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
(forall j, (j < 18)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (rgc_vals cx) 0)) /\
ew E 54 = Z_to_bv 64 (rga_F cx) /\ ew E 66 = Z_to_bv 64 (rga_FL cx) /\ ew E 67 = Z_to_bv 64 (SB + rga_F cx / 8).
Definition rga_post (B : asyms) (cx : rgcx) : world trasegs -> config -> Prop :=
trgb_addframe_postV B (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
(c_r cx) (c_g cx) (c_wfn cx) (c_ctx cx) (c_path cx) (c_attr cx) (c_gen cx) (c_loops cx) (c_Wd cx) (c_Hd cx) (c_bef cx) (c_beffmt cx)
(c_s cx) (c_N cx) (c_img cx) (c_fmt cx) (c_rest cx).
Definition rga_inv_t : Type := rgcx -> env -> Z -> alayout -> astate -> world trasegs -> machine_state -> Model -> Prop.
Definition rga_from_fp (FPx : rgcx -> list (Z * Z)) (B : asyms) (ss : sstate) (INV : rga_inv_t) : Prop :=
forall (cx : rgcx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rga_base B cx -> rga_E cx E -> frm_zero fp_csr ->
ajournal trasegs B TRGBADD_STK (spZ (c_regs cx)) (FPx cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(7, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (7, c_fpos cx) :: frames (c_S cx) ->
INV cx E k ly3 S3 W3 ms3 md3 ->
st_ok trasegs E ss (restrict (w_H W3) ms3) ->
SRr trasegs W3 (mkCfg ms3 md3) (rga_post B cx).
Definition rga_from := rga_from_fp rgc_FPs.
Definition rga_fromF := rga_from_fp rgc_FP.
Definition RGA_G : Z := 71.
Definition RGA_T : Z := 509.
Definition rga_bud (cx : rgcx) (S3 : astate) (k g t a : Z) : Prop :=
bud_le (c_S cx) S3 k (g + t + a) (2 ^ 17 * (g + a) + 208 * t) (GH * g + HULL_UNIT * a).
Definition rga_kb (cx : rgcx) (S3 : astate) (k : Z) (K : Prop) (g t a : Z) : Prop := K /\ rga_bud cx S3 k g t a.

Lemma rga_bud_of_gbud : forall cx S3 k, gbud (c_S cx) S3 k -> rga_bud cx S3 k k 0 0.
Proof. intros cx S3 k H. unfold rga_bud, gbud in *. eapply bud_le_mono; [exact H | unfold GH, HULL_UNIT; lia ..]. Qed.
Lemma gbud_of_rga_bud : forall cx S3 k, rga_bud cx S3 k k 0 0 -> gbud (c_S cx) S3 k.
Proof. intros cx S3 k H. unfold rga_bud, gbud in *. eapply bud_le_mono; [exact H | unfold GH, HULL_UNIT; lia ..]. Qed.
Lemma vev_room_strict : forall s j, vev s + (j + 1) <= VEV_MAX -> vev s + j < VEV_MAX.
Proof. intros s j H. lia. Qed.
Definition INV_0 (B : asyms) (kmax : Z) : rga_inv_t :=
fun cx E k ly3 S3 W3 ms3 md3 => rga_kb cx S3 k (k <= kmax) k 0 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\ blocks_bytes S3 = blocks_bytes (c_S cx).
End b.
Ltac rga_unf := idtac.
Ltac rga_eq c := let v := eval vm_compute in c in let H := fresh "Hcv" in assert (H : c = v) by reflexivity.
Ltac rga_consts := rga_eq EV_RGBADD; rga_eq EV_ADDFRAME; rga_eq EV_FREECHT; rga_eq EV_NTN; rga_unf;
unfold EV_FRAMEV, CN_FRAME, WT_FRAME, HL_FRAME, RGA_G, RGA_T, GH, HULL_UNIT.
Ltac rga_lia := rga_consts; lia.
Ltac rga_side := first [ solve [repeat match goal with K : _ |- _ => clear K end; rga_lia] | rga_lia ].
Ltac rga_chain_to H G kont :=
lazymatch type of H with
| bud_le _ G _ _ _ _ => kont H
| bud_le _ ?A _ _ _ _ =>
match goal with
| Hd : bud_le A ?C _ _ _ _ |- _ =>
let H2 := fresh "Hbc" in pose proof (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ H Hd) as H2; rga_chain_to H2 G kont
end
end.
Ltac rga_bud_tac Hbud :=
let Hb := fresh "Hb" in
pose proof Hbud as Hb; unfold rga_bud in Hb |- *; cbn [c_S] in Hb |- *;
lazymatch goal with |- bud_le _ ?G _ _ _ _ => rga_chain_to Hb G ltac:(fun H => eapply bud_le_mono; [exact H | ..]) end; rga_side.
Ltac rga_bud_auto := lazymatch goal with Hb0 : rga_bud _ _ _ _ _ _ |- _ => rga_bud_tac Hb0 end.
Ltac rga_room Hev Hbud :=
let Hb := fresh "Hb" in
pose proof Hbud as Hb; unfold rga_bud in Hb; cbn [c_S] in Hb;
lazymatch goal with
| |- vev ?Sc + _ <= VEV_MAX => rga_chain_to Hb Sc ltac:(fun H => eapply (vev_room_of_bud _ _ _ _ _ _ _ _ _ _ _ Hev H))
| |- vev ?Sc + _ < VEV_MAX => apply vev_room_strict; rga_chain_to Hb Sc ltac:(fun H => eapply (vev_room_of_bud _ _ _ _ _ _ _ _ _ _ _ Hev H))
| |- vev ?Sc < VEV_MAX => rga_chain_to Hb Sc ltac:(fun H => eapply (vev_lt_of_bud _ _ _ _ _ _ _ _ _ _ Hev H))
| |- bud_ok ?Sc _ _ _ _ => rga_chain_to Hb Sc ltac:(fun H => eapply (bud_ok_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hev H))
end.
Definition rga_fromA {rc : YN05.RunCeil} (B : asyms) (ss : sstate) (INV : forall fx : YK11.FPState, rga_inv_t) : Prop :=
forall fx : YK11.FPState, @rga_from fx rc B ss (INV fx).
Definition rga_fromFA {rc : YN05.RunCeil} (B : asyms) (ss : sstate) (INV : forall fx : YK11.FPState, rga_inv_t) : Prop :=
forall fx : YK11.FPState, @rga_fromF fx rc B ss (INV fx).
