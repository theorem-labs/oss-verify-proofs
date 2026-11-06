(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module paths and module names changed; 350 of its 393 lines of code are new or changed and 283 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW14Ask.v at 2d46ab19875e, with the parts of
   proofs/reac-pw/fuzz_rate/lib/A/RtPgW14Base.v at 2d46ab19875e it uses (the code table, the run tactic, w14_r234),
   for image B (fuzz_rate.asan-ubsan): image B's pcs (A 0x82dec -> DEC 0x82e44, 22 words) and registers; asked[0] and
   asked[1] are the real-frame cells R+0x198 / R+0x19c (two write windows of the real frame at s1) instead of two
   objects of the frame for locals, so the two scope stores, their shadow-byte regions and the shadow-pattern change go
   away (the frame's shadow stays rsb_PB); the hz cell is at F+0x2a0; the cuts are lib/AU/RtPgSegB.v's and the shared
   M02 layer is lib/AU/RtPgM02BaseB.v's. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's). Proves no
   function (kind: segment lemma): the piece W14-asked of LLVMFuzzerTestOneInput's segment M02, whose statement is
   lib/AU/RtPgSegB.v's rsb_piece_W14_asked_stmt; nothing here restates a cut.

   THE ASKED SET-UP (rsb_cut_A at A 0x82dec -> rsb_cut_DEC at DEC 0x82e44, turn 0), fuzz_rate.c:262:
     0x82dec ld a0,0x38(s1) (b5); ld a1,0x30(s1) (b6 << 8); or a0,a1,a0; ld a1,0x48(s1) (b3); ld a2,0x40(s1)
             (b4 << 8); or a1,a2,a1; li a2,1; slli a0,a0,16; or a0,a1,a0 (other); slli a1,s7,62 (s7 = the flags
             byte);
     0x82e14 bne s10,a2 -> 0x82e20 (s10 = rc); lw a2,0(s5) (the hz cell F+0x2a0); j 0x82e28; 0x82e20 a2 := 48000;
     0x82e28 li s10,0 (the turn); srli s5,a1,63 (the role, bit 1 of the flags byte); sw a2,0x198(s1) (asked[0]);
             sw a0,0x19c(s1) (asked[1]); auipc/addi s2 = 0x21520 (closed_list); li s9,2 (the turns' bound).
   No instrumented check, no scope store and no shadow store lies in it, so it is one run of the plain engine (YCbq
   aj_run over w14a_tbl) from an entry state with four regions: the real frame's four header cells R+0x30 / 0x38 /
   0x40 / 0x48 at s1 (read only, their values the header cells of rsb_Hc as env atoms 33 / 34 / 35 / 32), the hz
   cell at s5 (env atom 36, rsb_hz_at), and asked[0] and asked[1], two 4-byte write windows of the real frame at s1
   (atom 9), which lie in the journal's stack window (RtPgM02BaseB.m2b_awr). s10 is the literal rc: the parse's answer
   is rc = 1, 0 or -1 (Rate.answer_ok, w14a_rc3), and the engine decides `bne s10,a2` itself in each case.
   - asked[0] = rc = 1 ? hz : 48000: the run leaves CVal 4 (sext32 of the hz atom), whose low 4 bytes are hz's
     (w14a_sext32_low), or CVal 4 48000;
   - asked[1] = other: the run leaves CVal 4 of the `or` tree of the four cells, whose value is rsb_other
     (w14a_U_other, w14a_other_val: b3 + 256 b4 + 65536 (b5 + 256 b6) < 2^32 by rt_hdr_ok);
   - s5 = bit 1 of the flags byte: checked over the 256 byte values (w14a_bit1);
   - every byte the DEC cut names (the frame's shadow rsb_PB, the image, the first block, the real-frame cells below
     R+0x198) is outside the run's write window [R+0x198, R+0x1a0) (w14a_wr), so it is kept; that window is in
     M02's write set (RtPgImgB.hi_w2 holds (XR, 0x198, 8)).

   SECTION HYPOTHESIS of rt_w14_asked_B (Section m): MTL : ameter_laws MT. The frame's laws are the kernel theorem
   YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB RtPgStepsB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgM02BaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================= the image ======================================= *)
(* the 22 words 0x82dec .. 0x82e40 (the asked[] set-up); the stop pc DEC 0x82e44 lies outside it *)
Definition w14a_tbl : ctable := Eval vm_compute in (build_table rsegs RSB_A 22 TEmpty).
Lemma w14a_tbl_eq : w14a_tbl = build_table rsegs RSB_A 22 TEmpty.
Proof. vm_cast_no_check (eq_refl w14a_tbl). Qed.
Lemma w14a_tbl_ok : table_ok rsegs w14a_tbl.
Proof. rewrite w14a_tbl_eq. apply build_table_ok0. unfold RSB_A. lia. Qed.

(* No instrumented check lies in the range, so the run is the plain engine's (YCbq aj_run): no shadow entry and no
   static shadow check. *)
Ltac w14a_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
aj_run w14a_tbl_ok HS HJ; [awr | ] end.

(* sp / gp / tp kept by a run that leaves their atoms in place *)
Lemma w14a_r234 : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).
Proof.
intros r1 r2 H r Hr; destruct Hr as [Hr|[Hr|Hr]]; subst r; apply H; cbv [In];
repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* ======================================= the run's regions ======================================= *)
(* the real frame's four header cells the set-up reads, as env atoms 33, 34, 35, 32 (by offset) *)
Definition w14a_rframe : YP09.region := m2b_frame 0x30 0x50 0 0
  [YP09.mkChunk 0x30 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 34 0));
   YP09.mkChunk 0x40 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 32 0))].
(* the hz cell at s5 = F + 0x2a0, its 4 bytes the env atom 36 *)
Definition w14a_rhz : YP09.region := m2b_hzcell (SOff 36 0).
(* a 4-byte cell of the real frame at s1 = R + o, writable *)
Definition w14a_rask (o : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) o (o + 4) o (o + 4) cs.
Definition w14a_rs : smem := [w14a_rframe; w14a_rhz; w14a_rask 0x198 []; w14a_rask 0x19c []].
Definition w14a_extra (e : rt_renv) (hz : Z) : list word :=
  [w64 (q_b3 e); w64 (Z.shiftl (q_b6 e) 8); w64 (q_b5 e); w64 (Z.shiftl (q_b4 e) 8); w64 (hz mod 2 ^ 32)].
(* the value the run stores to asked[1]: (b4 << 8 | b3) | (b6 << 8 | b5) << 16 over the cells' atoms *)
Definition w14a_other_sv : sv :=
  SAlu ALU_OR (SAlu ALU_OR (SOff 35 0) (SOff 32 0)) (SAlu ALU_SLL (SAlu ALU_OR (SOff 33 0) (SOff 34 0)) (SLit 16)).
(* the run's write window: asked[0] and asked[1], [R + 0x198, R + 0x1a0) *)
Definition w14a_wr (R : Z) (a : Z) : Prop := R + 0x198 <= a < R + 0x1a0.

(* every write window of the run lies in w14a_wr *)
Ltac w14a_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
unfold w14a_wr;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  first [ lazymatch goal with E9 : bv_unsigned (ew _ 9) = _ |- _ => rewrite E9 in Hb end; lia | lia ] | ]);
destruct Hr.

(* ======================================= arithmetic ======================================= *)
(* 0x82e10 slli a1,s7,62; 0x82e2c srli s5,a1,63: s5 = bit 1 of the flags byte, over its 256 values *)
Lemma w14a_bits_all : forallb (fun n =>
  bv_eqb (alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 62)) (Z_to_bv 64 63))
    (Z_to_bv 64 (Z.b2z (Z.testbit (Z.of_nat n) 1)))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w14a_bit1 : forall fl, 0 <= fl < 256 ->
alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 fl) (Z_to_bv 64 62)) (Z_to_bv 64 63) = Z_to_bv 64 (Z.b2z (Z.testbit fl 1)).
Proof.
intros fl Hfl. pose proof w14a_bits_all as H. rewrite forallb_forall in H.
specialize (H (Z.to_nat fl) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply bv_eqb_eq in H. exact H.
Qed.

(* `or` of a byte and a byte shifted by 8 *)
Lemma w14a_lor8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (Z.shiftl y 8) x = x + 256 * y.
Proof.
intros x y Hx Hy. rewrite Z.lor_comm. rewrite lor_shiftl_add by (cbn; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. ring.
Qed.
Lemma w14a_other_val : forall e, rt_hdr_ok e ->
rsb_other e = q_b3 e + 256 * q_b4 e + 65536 * (q_b5 e + 256 * q_b6 e).
Proof.
intros e (_ & _ & _ & H3 & H4 & H5 & H6). unfold rsb_other.
rewrite (w14a_lor8 (q_b3 e) (q_b4 e)) by lia. rewrite (w14a_lor8 (q_b5 e) (q_b6 e)) by lia.
rewrite lor_shiftl_add by (cbn; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. ring.
Qed.
Lemma w14a_U_other : forall E b3 b4 b5 b6,
ew E 32 = Z_to_bv 64 b3 -> ew E 33 = Z_to_bv 64 (Z.shiftl b6 8) -> ew E 34 = Z_to_bv 64 b5 ->
ew E 35 = Z_to_bv 64 (Z.shiftl b4 8) ->
0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
U E w14a_other_sv = b3 + 256 * b4 + 65536 * (b5 + 256 * b6).
Proof.
intros E b3 b4 b5 b6 E32 E33 E34 E35 H3 H4 H5 H6.
assert (S4 : Z.shiftl b4 8 = 256 * b4) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; ring).
assert (S6 : Z.shiftl b6 8 = 256 * b6) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; ring).
unfold w14a_other_sv. rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom E 35 _ E35) by (rewrite S4; lia). rewrite (U_atom E 32 _ E32) by lia.
rewrite (U_atom E 33 _ E33) by (rewrite S6; lia). rewrite (U_atom E 34 _ E34) by lia.
rewrite (w14a_lor8 b3 b4) by lia. rewrite (w14a_lor8 b5 b6) by lia.
change (Z.land (zcanon 16) 63) with 16.
rewrite (zcanon_id (b3 + 256 * b4)) by (unfold M64; lia).
rewrite (zcanon_id (b5 + 256 * b6)) by (unfold M64; lia).
assert (SH : Z.shiftl (b5 + 256 * b6) 16 = (b5 + 256 * b6) * 65536)
by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (zcanon_id (Z.shiftl (b5 + 256 * b6) 16)) by (rewrite SH; unfold M64; lia).
rewrite lor_shiftl_add by (cbn; lia). rewrite SH. rewrite zcanon_id by (unfold M64; lia). ring.
Qed.

(* the low 4 bytes of a sign-extended 32-bit value are the value *)
Lemma w14a_sext32_low : forall c, 0 <= c < 2 ^ 32 -> zcanon (bv_swrap 32 c) mod 2 ^ 32 = c.
Proof.
intros c Hc. unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (2 ^ 32) with 4294967296 in *. change (2 ^ 64) with 18446744073709551616.
destruct (Z.lt_ge_cases c 2147483648) as [Hl|Hg].
- rewrite (Z.mod_small (c + 2147483648) 4294967296) by lia.
  replace (c + 2147483648 - 2147483648) with c by ring.
  rewrite (Z.mod_small c 18446744073709551616) by lia. apply Z.mod_small. lia.
- rewrite <- (Z.mod_unique (c + 2147483648) 4294967296 1 (c - 2147483648)) by lia.
  rewrite <- (Z.mod_unique (c - 2147483648 - 2147483648) 18446744073709551616 (-1)
    (c - 4294967296 + 18446744073709551616)) by lia.
  rewrite <- (Z.mod_unique (c - 4294967296 + 18446744073709551616) 4294967296 4294967295 c) by lia.
  reflexivity.
Qed.

(* the parse's answer is rc = 1, 0 or -1 (Rate.answer_ok of the parse and of the NULL answer) *)
Lemma w14a_rc3 : forall null bs,
snd (Rate.harness_parse null bs) = 1 \/ snd (Rate.harness_parse null bs) = 0 \/
snd (Rate.harness_parse null bs) = -1.
Proof.
intros null bs. unfold Rate.harness_parse. destruct null; [right; right; reflexivity|].
pose proof (Rate.parse_model_shape bs) as H.
destruct (Rate.parse_model bs) as [[v|] r]; cbn [snd Rate.answer_ok] in H |- *.
- left. exact (proj1 H).
- destruct H as [-> | ->]; [right; left | right; right]; reflexivity.
Qed.

(* ======================================= the run ======================================= *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* asked[]'s writes are in M02's write set: hi_w2's last range (XR, 0x198, 8) *)
Lemma w14a_wr_E2 : forall (cx : rsb_scx rsegs) a, w14a_wr (q_R (x_e rsegs cx)) a -> rsb_E2 rsegs cx a.
Proof.
intros cx a Hw. unfold rsb_E2, rt_inw. left. cbn [hi_w2 rate_himg_B]. rewrite !Exists_cons.
right; right; right; right; right; left. cbn [rt_xv fst snd]. unfold w14a_wr in Hw. lia.
Qed.

(* what reaching DEC from the set-up means: rsb_core, s0 / s1 / s3 / s4 / s6 as at A, the four registers turn 0
   sets (s2 = closed_list, s5 = the role, s9 = 2, s10 = 0), every byte outside the write window as at A, and asked[]
   filled *)
Definition w14a_AK (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (rec : pod_rec)
(regs0 : bvmap 5 word) (W0 : world rsegs) (mem0 : word -> option byte) : Prop :=
forall ly3 S3 regs3 mem3 md3,
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W0 regs3 mem3 md3 ->
cs_eq [8; 9; 19; 20; 22]%bv regs0 regs3 ->
getr regs3 (Z_to_bv 5 18) = w64 RSB_CLOSED ->
getr regs3 (Z_to_bv 5 21) = w64 (Z.b2z (Z.testbit (q_fl (x_e rsegs cx)) 1)) ->
getr regs3 (Z_to_bv 5 25) = w64 2 -> getr regs3 (Z_to_bv 5 26) = w64 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w14a_wr (q_R (x_e rsegs cx)) a ->
 aview rsegs (w_H W0) mem3 a = aview rsegs (w_H W0) mem0 a) ->
rsb_ask_at rsegs cx rec W0 mem3 ->
SRr rsegs W0 (cfg_at rsegs RSB_DEC regs3 mem3 md3) POST.

Lemma w14a_set : forall (cx : rsb_scx rsegs) POST rec ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rsb_at_cx rsegs cx W2 mem2 regs2
  (rsb_L_chk rsegs cx ++ [(LReg 26, snd (rsb_PA rsegs cx rec)); (LReg 22, q_mask (x_e rsegs cx));
                          (LReg 23, q_fl (x_e rsegs cx)); (LCell XR 0x60, q_F (x_e rsegs cx));
                          (LCell XR 0x168, q_pp (x_e rsegs cx))]) ->
rsb_hz_at rsegs cx rec W2 mem2 ->
w14a_AK cx POST rec regs2 W2 mem2 ->
SRr rsegs W2 (cfg_at rsegs RSB_A regs2 mem2 md2) POST.
Proof using MTL.
intros cx POST rec ly2 S2 W2 regs2 mem2 md2 Hpre Hcore Hat Hhz HK.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in Hwin, Hceil.
pose proof Hpre as Hp. unfold rsb_pre, rt_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhdr & _).
pose proof Hhdr as (Hfl & Hmask & _ & Hb3 & Hb4 & Hb5 & Hb6).
pose proof (proj1 Hcore) as HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
(* the cut's registers and cells *)
unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc in Hat. cbv zeta in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (((A8 & A9 & A19 & A20 & C178 & A21 & C10 & C50 & _) & (C48 & C30 & C38 & C40 & C18 & C148 & _)) &
  A26 & A22 & A23 & C60 & C168 & _).
cbn [rt_at rt_xv fst snd] in A9, A21, A26, A23, C48, C30, C38, C40.
assert (Sh4 : 0 <= Z.shiftl (q_b4 (x_e rsegs cx)) 8 < 65536)
by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
assert (Sh6 : 0 <= Z.shiftl (q_b6 (x_e rsegs cx)) 8 < 65536)
by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
rewrite Z.mod_small in C48, C30, C38, C40 by lia.
pose proof (Z.mod_pos_bound (rsb_hz rsegs cx rec) (2 ^ 32) ltac:(lia)) as Hhz32.
(* the entry state's env facts *)
set (X := w14a_extra (x_e rsegs cx) (rsb_hz rsegs cx rec)).
assert (E9 : bv_unsigned (ew (Ereg regs2 X) 9) = q_R (x_e rsegs cx)).
{ rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). assert (G : getr regs2 9%bv = w64 (q_R (x_e rsegs cx))) by exact A9.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E21 : bv_unsigned (ew (Ereg regs2 X) 21) = q_F (x_e rsegs cx) + 0x2a0).
{ rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl).
  assert (G : getr regs2 21%bv = w64 (q_F (x_e rsegs cx) + 0x2a0)) by exact A21.
  rewrite G. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : ew (Ereg regs2 X) 23 = w64 (q_fl (x_e rsegs cx))).
{ rewrite (ew_Ereg_nat regs2 _ 23 23%bv eq_refl). exact A23. }
assert (X32 : ew (Ereg regs2 X) 32 = w64 (q_b3 (x_e rsegs cx))) by exact (ew_Ereg_extra regs2 X 0).
assert (X33 : ew (Ereg regs2 X) 33 = w64 (Z.shiftl (q_b6 (x_e rsegs cx)) 8)) by exact (ew_Ereg_extra regs2 X 1).
assert (X34 : ew (Ereg regs2 X) 34 = w64 (q_b5 (x_e rsegs cx))) by exact (ew_Ereg_extra regs2 X 2).
assert (X35 : ew (Ereg regs2 X) 35 = w64 (Z.shiftl (q_b4 (x_e rsegs cx)) 8)) by exact (ew_Ereg_extra regs2 X 3).
assert (X36 : ew (Ereg regs2 X) 36 = w64 (rsb_hz rsegs cx rec mod 2 ^ 32)) by exact (ew_Ereg_extra regs2 X 4).
(* the regions *)
assert (HRS : Forall (region_ok rsegs (Ereg regs2 X) (mrestrict (w_H W2) mem2)) w14a_rs).
{ unfold w14a_rs. repeat apply Forall_cons; try apply Forall_nil.
  - unfold w14a_rframe.
    apply (m2b_frame_ok _ W2 mem2 (q_R (x_e rsegs cx)) (x_STK rsegs cx) (x_sp0 rsegs cx));
    [exact E9 | lia | lia | exact Hpres | lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val rsegs _ _ _ 0x30 8 (SOff 33 0) (Z.shiftl (q_b6 (x_e rsegs cx)) 8));
      [apply rtsb_den_atom; [exact X33 | lia] | cbn; lia | cbn; lia | exact C30].
    + apply (chunk_ok_val rsegs _ _ _ 0x38 8 (SOff 34 0) (q_b5 (x_e rsegs cx)));
      [apply rtsb_den_atom; [exact X34 | lia] | cbn; lia | cbn; lia | exact C38].
    + apply (chunk_ok_val rsegs _ _ _ 0x40 8 (SOff 35 0) (Z.shiftl (q_b4 (x_e rsegs cx)) 8));
      [apply rtsb_den_atom; [exact X35 | lia] | cbn; lia | cbn; lia | exact C40].
    + apply (chunk_ok_val rsegs _ _ _ 0x48 8 (SOff 32 0) (q_b3 (x_e rsegs cx)));
      [apply rtsb_den_atom; [exact X32 | lia] | cbn; lia | cbn; lia | exact C48].
  - unfold w14a_rhz.
    apply (m2b_hzcell_ok _ W2 mem2 (q_F (x_e rsegs cx)) (SOff 36 0) (rsb_hz rsegs cx rec mod 2 ^ 32));
    [exact E21 | lia | lia | apply rtsb_den_atom; [exact X36 | lia] | lia | exact Hhz].
  - unfold w14a_rask. apply (rtmb_rw_region rsegs _ (w_H W2) mem2 9 (q_R (x_e rsegs cx)));
    [exact E9 | lia | lia | | apply Forall_nil].
    intros o Ho. apply Hpres. lia.
  - unfold w14a_rask. apply (rtmb_rw_region rsegs _ (w_H W2) mem2 9 (q_R (x_e rsegs cx)));
    [exact E9 | lia | lia | | apply Forall_nil].
    intros o Ho. apply Hpres. lia. }
assert (HPD : pairwise_disjoint (Ereg regs2 X) w14a_rs).
{ unfold w14a_rs, w14a_rframe, w14a_rhz, w14a_rask, m2b_frame, m2b_hzcell.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E21.
  repeat split; lia. }
pose proof (m2b_facts_ok (Ereg regs2 X) (q_R (x_e rsegs cx)) E9 ltac:(lia) Hal) as HG.
(* the three answers of the parse *)
destruct (w14a_rc3 (Z.testbit (q_fl (x_e rsegs cx)) 0) (buf rec)) as [Hrc|[Hrc|Hrc]];
change (Rate.harness_parse (Z.testbit (q_fl (x_e rsegs cx)) 0) (buf rec)) with (rsb_PA rsegs cx rec) in Hrc;
rewrite Hrc in A26;
lazymatch type of A26 with _ = w64 ?v =>
pose proof (m2b_entry RSB_A [((26%bv : bv 5), SLit v)] w14a_rs m2b_facts W2 regs2 X mem2) as HS;
specialize (HS ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split;
  [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz
  | rewrite ck_lit; symmetry; exact A26]) ltac:(vm_compute; reflexivity) HRS HPD HG)
end;
remember (Ereg regs2 X) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs2 X) E) by (subst E; apply env_agree_refl);
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w14a_wr (q_R (x_e rsegs cx)) a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity);
unfold cfg_at; change (w64 RSB_A) with (Z_to_bv 64 RSB_A);
w14a_run idtac.
1,3,5: m2b_awr.
all: ck_keep w14a_kwr.
all: let R := fresh "R18" in rreg HS (18%bv : bv 5) R.
all: let R := fresh "R21" in rreg HS (21%bv : bv 5) R.
all: let R := fresh "R25" in rreg HS (25%bv : bv 5) R.
all: let R := fresh "R26" in rreg HS (26%bv : bv 5) R.
all: lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [8; 9; 19; 20; 22]%bv HS HAE ltac:(vm_compute; reflexivity)) as CL;
  pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
  pose proof (rtsb_region_nth E ss ms 2 _ H HS eq_refl) as G0;
  pose proof (rtsb_region_nth E ss ms 3 _ H HS eq_refl) as G1;
  rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
  replace (ss_pc ss) with RSB_DEC by (vm_compute; reflexivity)
  end.
all: lazymatch goal with HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _ |- _ =>
  apply (HK ly2 S2 (ms_regs ms) (ms_mem ms) mdT);
  [ apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ'
      (w14a_r234 _ _ C234) eq_refl (Permutation_refl _)); [m2b_io | apply (mo_le_refl MT MTL) |];
    intros a Ha _ He; apply KE; [exact Ha | intros Hw; exact (He (w14a_wr_E2 cx a Hw))]
  | exact CL | | | | | exact KE | ]
  end.
(* s2 = closed_list, s5 = the role, s9 = 2, s10 = 0 *)
all: try exact R18.
all: try (etransitivity; [exact R21|]; rewrite E23; exact (w14a_bit1 _ Hfl)).
all: try exact R25.
all: try exact R26.
(* asked[0] and asked[1] *)
all: split.
all: try (refine (val_of_chunk_ok rsegs E _ _ 0x19c 4 w14a_other_sv (rsb_other (x_e rsegs cx)) _ _ _ ltac:(cbn; lia));
  [ exact (rtsb_chunks E _ 9 _ _ _ _ _ _ G1 E9 _ (or_introl eq_refl))
  | rewrite denot_lit_U; f_equal;
    rewrite (w14a_U_other E _ _ _ _ X32 X33 X34 X35 Hb3 Hb4 Hb5 Hb6), (w14a_other_val _ Hhdr); reflexivity
  | rewrite (w14a_other_val _ Hhdr); cbn; lia ]).
(* asked[0]: rc = 1 stores the hz atom sign-extended, else 48000 *)
all: assert (A0 : rsb_ask0 rsegs cx rec = if snd (rsb_PA rsegs cx rec) =? 1 then rsb_hz rsegs cx rec else 48000)
  by reflexivity.
all: rewrite A0, Hrc; cbn [Z.eqb Pos.eqb].
- intros k Hk.
  refine (YN0d.chunk_bytes_cval rsegs E _ _ 0x198 4 (SExt true 32 (SOff 36 0)) _ _ _ k Hk).
  + exact (rtsb_chunks E _ 9 _ _ _ _ _ _ G0 E9 _ (or_introl eq_refl)).
  + change (bv_unsigned (sv_denot E (SExt true 32 (SOff 36 0)))) with (U E (SExt true 32 (SOff 36 0))).
    rewrite U_SExt. cbv iota beta. rewrite (U_atom E 36 _ X36 ltac:(lia)).
    change (8 * Z.of_N 4) with 32. change (Z.of_N 32) with 32.
    rewrite (Z.mod_small (rsb_hz rsegs cx rec mod 2 ^ 32) (2 ^ 32)) by lia.
    rewrite w14a_sext32_low by lia. rewrite ?Z.mod_mod by lia. reflexivity.
- change (48000 mod 2 ^ 32) with 48000.
  refine (val_of_chunk_ok rsegs E _ _ 0x198 4 (SLit 48000) 48000 _ eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  exact (rtsb_chunks E _ 9 _ _ _ _ _ _ G0 E9 _ (or_introl eq_refl)).
- change (48000 mod 2 ^ 32) with 48000.
  refine (val_of_chunk_ok rsegs E _ _ 0x198 4 (SLit 48000) 48000 _ eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  exact (rtsb_chunks E _ 9 _ _ _ _ _ _ G0 E9 _ (or_introl eq_refl)).
Qed.
End w.

(* ======================================= the piece statement ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the DEC cut at turn 0 from the A cut's facts and what the set-up gives *)
Lemma w14a_cut_DEC : forall (cx : rsb_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 regs3 mem3 md3,
rsb_pre rsegs B cx -> rsb_cut_A (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W2 regs3 mem3 md3 ->
cs_eq [8; 9; 19; 20; 22]%bv regs2 regs3 ->
getr regs3 (Z_to_bv 5 18) = w64 RSB_CLOSED ->
getr regs3 (Z_to_bv 5 21) = w64 (Z.b2z (Z.testbit (q_fl (x_e rsegs cx)) 1)) ->
getr regs3 (Z_to_bv 5 25) = w64 2 -> getr regs3 (Z_to_bv 5 26) = w64 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w14a_wr (q_R (x_e rsegs cx)) a ->
 aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rsb_ask_at rsegs cx rec W2 mem3 ->
rsb_cut_DEC (fx := fx) rsegs B MT cx fx2 rec 0 ly3 S3 W2 regs3 mem3 md3.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 regs3 mem3 md3 Hpre (Hbase & Hat & _) Hcore3 HL
H18 H21 H25 H26 K3 Hask.
destruct Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof rtsb_segs_low as Hsegs.
pose proof (m2b_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof (rtsb_fbounds _ F32 Fapp) as (_ & _ & S0 & S128 & _).
pose proof (m2b_pp B cx Hpre) as (P4096 & Pceil & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
unfold T_SEG_STK, ASTACK in Hceil.
(* every byte below the allocator's ceiling (the frame's shadow, the image, the first block) is outside the write
   window, which lies in the real frame above it *)
assert (Wfar : forall a, a < alloc_ceiling -> ~ w14a_wr (q_R (x_e rsegs cx)) a).
{ intros a Ha Hw. unfold w14a_wr in Hw. lia. }
unfold rsb_at_cx, rsb_at, rsb_L_chk, rsb_Hc in Hat. cbv zeta in Hat. rewrite !Forall_app, !Forall_cons_iff in Hat.
destruct Hat as (((A8 & A9 & A19 & A20 & C178 & A21 & C10 & C50 & _) & (C48 & C30 & C38 & C40 & C18 & C148 & _)) &
  A26 & A22 & A23 & C60 & C168 & _).
cbn [rt_at rt_xv fst snd] in A8, A9, A19, A20, A22, C178, C10, C18, C148, C60, C168.
assert (Kc : forall o v, 0 <= o -> o + 8 <= 0x198 ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (q_R (x_e rsegs cx) + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (q_R (x_e rsegs cx) + o) 8 v).
{ intros o v Ho1 Ho2 Hv. eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K3; [lia|]. unfold w14a_wr. lia. }
split; [|split; [|split; [exact Hask | lia]]].
- (* rsb_chk_base: everything the A cut gave, kept *)
  split; [exact Hcore3|]. split; [exact Hfxk|].
  split.
  { unfold rsb_fsh_at in *. apply (rtmb_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi.
    change (Z.of_nat (length rsb_PB)) with 88 in Hi.
    apply K3; [lia | apply Wfar; lia]. }
  split.
  { apply (rtmb_rom_kept rsegs W2 W2 mem2 mem3 Hrom). intros a Ha.
    assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    pose proof (Hsegs a Hi) as Hlow. rewrite C5 in Hlow.
    apply K3; [lia | apply Wfar; lia]. }
  split.
  { unfold rsb_pp_at in *. intros j Hj. destruct (Hpp j Hj) as (Hv & Hr). split; [|exact Hr].
    unfold rsb_u8s in Hj. rewrite length_map in Hj. pose proof (Layout.length_pp_bytes rec Hwf) as HL0.
    eapply (val_mem_kept rsegs); [|exact Hv]. intros k Hk. change (Z.of_nat 1) with 1 in Hk.
    apply K3; [lia | apply Wfar; lia]. }
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|]. split; [exact Hpod | exact Hpod1].
- (* the turn-0 values *)
  unfold rsb_at_cx, rsb_at, rsb_L_DEC, rsb_L_dec. cbv zeta. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
  + etransitivity; [exact (HL 8%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A8.
  + etransitivity; [exact (HL 9%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A9.
  + etransitivity; [exact (HL 19%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A19.
  + exact (Kc 0x10 _ ltac:(lia) ltac:(lia) C10).
  + exact (Kc 0x18 _ ltac:(lia) ltac:(lia) C18).
  + exact (Kc 0x60 _ ltac:(lia) ltac:(lia) C60).
  + exact (Kc 0x168 _ ltac:(lia) ltac:(lia) C168).
  + exact (Kc 0x148 _ ltac:(lia) ltac:(lia) C148).
  + exact (Kc 0x178 _ ltac:(lia) ltac:(lia) C178).
  + etransitivity; [exact (HL 20%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A20.
  + rewrite H26. reflexivity.
  + exact H25.
  + exact H21.
  + etransitivity; [exact (HL 22%bv ltac:(cbv [In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].
    exact A22.
  + exact H18.
Qed.

(* ---- W14 ASKED: A 0x82dec -> DEC 0x82e44, turn 0 ---- *)
Theorem rt_w14_asked_B : rsb_piece_W14_asked_stmt rsegs B MT.
Proof using MTL.
unfold rsb_piece_W14_asked_stmt. intros cx POST inp Hst HDEC.
unfold rsb_from_A. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HA.
destruct Hst as (Hpre & _).
pose proof HA as (Hbase & Hat & Hhz). pose proof Hbase as (Hcore & _).
apply (w14a_set (fx := fx2) B MT MTL cx POST rec ly2 S2 W2 regs2 mem2 md2 Hpre Hcore Hat Hhz).
intros ly3 S3 regs3 mem3 md3 Hcore3 HL H18 H21 H25 H26 K3 Hask.
apply (HDEC fx2 ly3 S3 W2 regs3 mem3 md3 rec).
exact (w14a_cut_DEC cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 regs3 mem3 md3 Hpre HA Hcore3 HL
  H18 H21 H25 H26 K3 Hask).
Qed.
End m.

Print Assumptions rt_w14_asked_B.
About rt_w14_asked_B.
