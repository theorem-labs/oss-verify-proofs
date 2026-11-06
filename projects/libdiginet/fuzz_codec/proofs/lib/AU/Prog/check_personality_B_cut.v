(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: cw_fresh, cw_kept0, cw_kept_step and cw_kept_call are the text of
   proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v:63-153 (origin/ossv/recipes 4b6f0df50aa7: sbd_fresh,
   sbd_kept0, sbd_kept_step, sbd_kept_call), with the segment list made image A's tfibsegs, the call's window a
   parameter and the world after the call generalized, for libdiginet/fuzz_codec's ASan build; cw_kept_cj is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkKept.v, with its module paths and module names changed; 766 of its 850 lines of code are new or changed and 134 lines of the source are left out. *)
(* Image B: the cut of check_personality's walk (lib/AU/Prog/check_personality_B.v), image A's
   (lib/A/Prog/check_personality_A_cut.v) at image B's addresses: the function at 0x8391c (its instructions aligned
   with image A's; image B adds two 8-alignment checks of the personality pointers, which the engine decides on the
   pinned literals), the callees diginet_personality_of 0x8513c, diginet_personality_from_name 0x85090 and the strcmp
   wrapper 0x42424, personalities[] at CB_PERS 0x9e240 (its announce-name pointers 0x213c0 / 0x213e0), the string rows
   CB_ROSTRS (each 0x60 above image A's), and the rows' bound below the stack 0x9f000 (page under CB_RHI 0x9f128).
   Image A's notes follow, with image B's addresses. *)
(* check_personality (fuzz_codec.c:256-281) at image B 0x8391c: the cuts of its walk and the facts every segment
   uses. The function calls diginet_personality_of three times, the strcmp wrapper twice and
   diginet_personality_from_name five times; the walk restarts the engine at each return address (a cut) from the
   concrete facts the call's post leaves, in the form of the start state at a cut of
   projects/libreac/fuzz_identity/proofs/lib/A/Prog/sb_dec_C.v (sbc_start).
   - cpctx: the entry context of the call (the contract's quantified variables); cp_ok: the contract's two
     premises on it; cp_post: its post.
   - A cut at pc (cp_cut): the journal from the caller's start, the frames, blocks, input and meter of the call
     state (cp_mem), what the call has kept of its entry memory (tcj_kept, window T_check_pers, nothing written
     outside it), the four 8-byte save slots [sp - 32, sp) holding the entry s2, s1, s0, ra, and the registers the
     walk relies on (cp_rg): sp - 32, gp, tp, s2 = SB and the entry s3 .. s11.
   - The start state at a cut (cp_start0 / cp_start1): atoms 33 .. 36 are the entry ra, s0, s1, s2; the save slots
     a read-only region of atom 2 (cp_save); the .got slot and the shadow-offset cell; with cp_start1 also the
     48 bytes of personalities[] as image bytes and their 6 shadow bytes (lib/A/Prog/CPgWalkImg.v). Registers whose
     value the cut fixes are pinned to that value (s2 to atom 32), so the engine folds the instrumented checks of
     the personalities' fields to loads of `SOff 32 off` and decides every branch. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgEncU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Rt Require Import StrcmpDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkRoU CPgWalkStrU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_CHECK_PERS : Z := 0x8391c.
Definition B_PERS_OF : Z := 0x8513c.
Definition B_FROM_NAME : Z := 0x85090.
Definition B_STRCMP : Z := 0x42424.

(* ================================ the context ================================ *)
Record cpctx := mkCP {
  c_STK : Z; c_sp0 : Z; c_FP : list (Z * Z); c_ly : alayout; c_S : astate; c_W0 : world tfibsegs;
  c_mem0 : word -> option byte; c_md0 : Model; c_own : list (Z * Z); c_lyc : alayout; c_Sc : astate;
  c_W : world tfibsegs; c_memc : word -> option byte; c_mdc : Model; c_k : Z; c_regs : bvmap 5 word }.

(* the rows of the image the call and its callees read: personalities[] and the 33 string literals *)
Definition CP_ROWS : list (Z * Z) := (CB_PERS, 48) :: CB_ROSTRS.
(* the registers each cut fixes: a0 after personality_of(1); a0 and s1 after personality_of(2); from the first strcmp
   on, a0 (the last call's result), s1 = &personalities[0], s0 = &personalities[1] *)
Definition cp_R1 (regs2 : bvmap 5 word) : Prop := getr regs2 10 = w64 CB_PERS.
Definition cp_R2 (regs2 : bvmap 5 word) : Prop := getr regs2 10 = w64 (CB_PERS + 24) /\ getr regs2 9 = w64 CB_PERS.
Definition cp_Rs (a0 : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 10 = w64 a0 /\ getr regs2 9 = w64 CB_PERS /\ getr regs2 8 = w64 (CB_PERS + 24).
Definition cp_pins1 : list (bv 5 * sv) := [(10%bv, SLit CB_PERS); (18%bv, SOff 32 0)].
Definition cp_pins2 : list (bv 5 * sv) := [(10%bv, SLit (CB_PERS + 24)); (9%bv, SLit CB_PERS); (18%bv, SOff 32 0)].
Definition cp_pins_s (a0 : Z) : list (bv 5 * sv) :=
[(10%bv, SLit a0); (9%bv, SLit CB_PERS); (8%bv, SLit (CB_PERS + 24)); (18%bv, SOff 32 0)].

(* the four save slots and the entry values they hold *)
Definition cp_xs (X : cpctx) : list Z :=
[raZ (c_regs X); bv_unsigned (getr (c_regs X) 8); bv_unsigned (getr (c_regs X) 9); bv_unsigned (getr (c_regs X) 18)].
Definition cp_save : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 32 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 36 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0));
 YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
Definition cp_rs0 : smem := [cp_save; got_region; bcell_region 32].
Definition cp_rs1 : smem := cp_rs0 ++ [cpg_img_region CB_PERS 48; cpg_shadow_region CB_PERS 48].
(* registers pinned at a cut *)
Definition cp_pin (pins : list (bv 5 * sv)) : list sv :=
fold_left (fun sr p => sr_set sr (fst p) (snd p)) pins sr_atoms.
Definition cp_E (X : cpctx) (regs2 : bvmap 5 word) : env := Ereg regs2 (cw_extra (cp_xs X)).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Definition cp_ok (B : asyms) (X : cpctx) : Prop :=
cdc_entry tfibsegs B (c_STK X) (c_sp0 X) (c_FP X) (c_ly X) (c_S X) (c_W0 X) (c_mem0 X) (c_md0 X) (c_own X)
  (c_lyc X) (c_Sc X) (c_W X) (c_memc X) (c_mdc X) (c_k X) (c_regs X) TB_check_pers /\
cimg_rd tfibsegs B CB_RLO CB_RHI (c_W X) (c_memc X) (spZ (c_regs X)) TB_check_pers CP_ROWS.
Definition cp_post (B : asyms) (MT : ameter_ops) (X : cpctx) : world tfibsegs -> config -> Prop :=
cdc_post tfibsegs B MT (c_STK X) (c_sp0 X) (c_FP X) (c_ly X) (c_S X) (c_W0 X) (c_mem0 X) (c_md0 X) (c_own X)
  (c_k X) (c_regs X) TB_check_pers cno_wr (c_lyc X) (c_Sc X) (c_W X) (c_memc X) (c_mdc X)
  (fun (_ : world tfibsegs) (_ : word -> option byte) (_ : bvmap 5 word) => True).
Definition cp_jr (B : asyms) (X : cpctx) ly2 S2 (W2 : world tfibsegs) mem2 md2 : Prop :=
ajournal tfibsegs B (c_STK X) (c_sp0 X) (c_FP X) (c_ly X) (c_S X) (c_W0 X) (c_mem0 X) (c_md0 X) (c_own X)
  ly2 S2 W2 mem2 md2 (c_k X).
Definition cp_slots (X : cpctx) (W2 : world tfibsegs) (mem2 : word -> option byte) : Prop :=
val_mem tfibsegs (mrestrict (w_H W2) mem2) (spZ (c_regs X) - 32) 8 (bv_unsigned (getr (c_regs X) 18)) /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (spZ (c_regs X) - 24) 8 (bv_unsigned (getr (c_regs X) 9)) /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (spZ (c_regs X) - 16) 8 (bv_unsigned (getr (c_regs X) 8)) /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (spZ (c_regs X) - 8) 8 (raZ (c_regs X)).
Definition cp_mem (B : asyms) (MT : ameter_ops) (X : cpctx) ly2 S2 (W2 : world tfibsegs) mem2 md2 : Prop :=
cp_jr B X ly2 S2 W2 mem2 md2 /\ frames S2 = frames (c_Sc X) /\
Permutation (ablocks B ly2 S2) (ablocks B (c_lyc X) (c_Sc X)) /\ same_io (c_mdc X) md2 /\ mo_le MT (c_Sc X) S2 0 /\
tcj_kept tfibsegs B TB_check_pers (c_lyc X) (c_Sc X) (c_W X) (c_memc X) W2 mem2 (spZ (c_regs X)) cno_wr /\
cp_slots X W2 mem2.
Definition cp_rg (X : cpctx) (regs2 : bvmap 5 word) : Prop :=
getr regs2 2 = w64 (spZ (c_regs X) - 32) /\ getr regs2 3 = getr (c_regs X) 3 /\ getr regs2 4 = getr (c_regs X) 4 /\
getr regs2 18 = w64 SB /\ (forall r, 19 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr (c_regs X) (Z_to_bv 5 r)).
Definition cp_cut (B : asyms) (MT : ameter_ops) (X : cpctx) (pc : Z) (Rg : bvmap 5 word -> Prop)
: world tfibsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs)) md2 /\
  cp_mem B MT X ly2 S2 W2 mem2 md2 /\ cp_rg X regs2 /\ Rg regs2.
(* the rest of the walk from a cut *)
Definition cp_rest (B : asyms) (MT : ameter_ops) (X : cpctx) (pc : Z) (Rg : bvmap 5 word -> Prop) : Prop :=
forall W2 c2, cp_cut B MT X pc Rg W2 c2 -> SRr tfibsegs W2 c2 (cp_post B MT X).

(* ================================ facts of the entry context ================================ *)
Lemma cp_ok_facts : forall B X, cp_ok B X ->
  AR tfibsegs B (c_lyc X) (c_Sc X) (c_W X) (c_memc X) (c_mdc X) /\
  alloc_ceiling <= spZ (c_regs X) - TB_check_pers /\ spZ (c_regs X) <= 2 ^ 47 /\
  2 ^ 46 + TB_check_pers <= spZ (c_regs X) /\ spZ (c_regs X) mod 16 = 0 /\
  c_sp0 X - c_STK X <= spZ (c_regs X) - TB_check_pers /\ spZ (c_regs X) <= c_sp0 X.
Proof.
intros B X (HE & _).
pose proof (cw_entry_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB_check_pers HE ltac:(unfold TB_check_pers, TB_from_name, ESTACK; lia))
  as (H1 & H2 & H3 & H4 & _).
pose proof HE as ((HAR & _) & _ & _ & _ & _ & _ & Hw1 & Hw2 & _).
split; [exact HAR|]. repeat split; assumption.
Qed.
Lemma cp_T : TB_check_pers = 8272.
Proof. reflexivity. Qed.

(* ================================ the rows of the image ================================ *)
Definition cp_row_chk (r : Z * Z) : bool :=
cpg_img_some (fst r) (snd r) && (0 <? snd r) && (IMG_LO + 64 <=? fst r) && (fst r + snd r + 64 <=? IMG_HI) &&
(fst r + snd r <=? 0x9f000) && existsb (fun p => (fst p =? fst r) && (snd p =? snd r)) CODEC_GLOBS.
Lemma cp_rows_chk : forallb cp_row_chk CP_ROWS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cp_row_facts : forall q n, In (q, n) CP_ROWS ->
  cpg_img_some q n = true /\ 0 < n /\ IMG_LO + 64 <= q /\ q + n + 64 <= IMG_HI /\ q + n <= 0x9f000 /\
  In (q, n) CODEC_GLOBS.
Proof.
intros q n Hin. pose proof (proj1 (forallb_forall _ _) cp_rows_chk (q, n) Hin) as H.
unfold cp_row_chk in H. cbn [fst snd] in H.
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?] end.
repeat match goal with Hb : (_ <? _) = true |- _ => apply Z.ltb_lt in Hb | Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb end.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
apply globs_In_b. assumption.
Qed.
(* personalities[] is a table of lib_const_addr *)
Lemma cp_rows_free_all : forall B, TfibLib B -> cpw_rows_free B CB_ROSTRS -> cpw_rows_free B CP_ROWS.
Proof.
intros B TL RF. unfold CP_ROWS, cpw_rows_free. apply Forall_cons; [|exact RF].
cbn [fst snd]. intros i Hi. apply (tl_lib_consts B TL). unfold lib_const_addr, CB_PERS. lia.
Qed.
(* a byte of the read-only window is a byte of the image *)
Lemma cp_ro_img : forall a, in_roP tfibsegs CB_RLO CB_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. unfold CB_RLO, CB_RHI in Hgot. lia.
Qed.
(* the read-only data is kept by what the call kept *)
Lemma cp_arodata_kept : forall B T lyc Sc (W : world tfibsegs) memc W2 mem2 sp E,
  tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp E ->
  arodata_okP tfibsegs CB_RLO CB_RHI B (aview tfibsegs (w_H W) memc) ->
  arodata_okP tfibsegs CB_RLO CB_RHI B (aview tfibsegs (w_H W2) mem2).
Proof.
intros B T lyc Sc W memc W2 mem2 sp E (_ & _ & K3 & _) HR a Hro Ho He.
rewrite (K3 a (cp_ro_img a Hro) Ho He). exact (HR a Hro Ho He).
Qed.

(* ================================ the image data ================================ *)
(* personalities[0] and [1]: the announce-name pointers and the four byte fields of each *)
Lemma cp_pers_bytes : cpw_img_list CB_PERS 48 =
[1; 0; 0; 0; 0; 0; 0; 0; 0xc0; 0x13; 2; 0; 0; 0; 0; 0; 1; 0x18; 4; 0x19; 0; 0; 0; 0;
 2; 0; 0; 0; 0; 0; 0; 0; 0xe0; 0x13; 2; 0; 0; 0; 0; 0; 0; 8; 8; 9; 0; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.
Lemma cp_u64 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. exact (bv_unsigned_in_range 64 w). Qed.
Lemma cp_in0 : forall l, existsb (Z.eqb 0) l = true -> In 0 l.
Proof. intros l H. apply existsb_exists in H as (x & Hx & He). apply Z.eqb_eq in He. subst x. exact Hx. Qed.
Lemma cp_r2 : Z_to_bv 5 2 = (2%bv : bv 5). Proof. apply bv_eq. reflexivity. Qed.
Lemma cp_r3 : Z_to_bv 5 3 = (3%bv : bv 5). Proof. apply bv_eq. reflexivity. Qed.
Lemma cp_r4 : Z_to_bv 5 4 = (4%bv : bv 5). Proof. apply bv_eq. reflexivity. Qed.
Lemma cp_r18 : Z_to_bv 5 18 = (18%bv : bv 5). Proof. apply bv_eq. reflexivity. Qed.
(* the pinned register file is ok when each pin holds *)
Lemma cp_pin_ok : forall E regs2 pins sr, regs_ok E sr regs2 ->
  Forall (fun p => fst p <> 0%bv /\ getr regs2 (fst p) = sv_denot E (snd p)) pins ->
  regs_ok E (fold_left (fun sr p => sr_set sr (fst p) (snd p)) pins sr) regs2.
Proof.
intros E regs2 pins. induction pins as [|p pins IH]; intros sr Hsr Hp; cbn [fold_left]; [exact Hsr|].
apply Forall_cons_iff in Hp as ((H0 & H1) & Hp). apply IH; [|exact Hp]. apply regs_ok_pin; assumption.
Qed.
(* sv_eqb-checked register values *)
Lemma cp_reg_atom : forall E' ss (H : word -> bool) ms (r : bv 5) n E0,
  st_ok tfibsegs E' ss (restrict H ms) -> sv_eqb (sr_get (ss_regs ss) r) (SOff n 0) = true -> (n < 37)%nat ->
  (forall n, (n < 37)%nat -> ew E' n = ew E0 n) -> getr (ms_regs ms) r = ew E0 n.
Proof.
intros E' ss H ms r n E0 HS Hc Hn HA.
rewrite (st_ok_restrict_reg tfibsegs H E' ss ms r HS), (sv_eqb_eq _ _ Hc). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply HA. exact Hn.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis RF : cpw_rows_free B CB_ROSTRS.
Variable X : cpctx.
Hypothesis HOK : cp_ok B X.
Local Notation SP := (spZ (c_regs X)).

Lemma cp_sp : 2 ^ 46 + 8272 <= SP /\ SP <= 2 ^ 47 /\ SP mod 16 = 0 /\ alloc_ceiling <= SP - 8272 /\
  c_sp0 X - c_STK X <= SP - 8272 /\ SP <= c_sp0 X.
Proof.
destruct (cp_ok_facts B X HOK) as (_ & H1 & H2 & H3 & H4 & H5 & H6). rewrite cp_T in *.
repeat split; assumption.
Qed.
Lemma cp_E_reg : forall regs2 (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cp_E X regs2) n = getr regs2 r.
Proof. intros regs2 n r H. exact (cw_ew_reg regs2 (cp_xs X) n r H). Qed.
Lemma cp_E2 : forall regs2, cp_rg X regs2 -> bv_unsigned (ew (cp_E X regs2) 2) = SP - 32.
Proof.
intros regs2 (R2 & _). destruct cp_sp as (H46 & H47 & _).
rewrite (cp_E_reg regs2 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia.
Qed.
Lemma cp_E32 : forall regs2, ew (cp_E X regs2) 32 = Z_to_bv 64 SB.
Proof. intros regs2. unfold cp_E. apply cw_ew_SB. Qed.

(* ================================ the start states ================================ *)
Lemma cp_save_ok : forall (W2 : world tfibsegs) regs2 mem2, cp_slots X W2 mem2 -> cp_rg X regs2 ->
  region_ok tfibsegs (cp_E X regs2) (mrestrict (w_H W2) mem2) cp_save.
Proof.
intros W2 regs2 mem2 (S1 & S2 & S3 & S4) HRG.
destruct cp_sp as (H46 & H47 & _).
assert (U2 : base_val (cp_E X regs2) (Some 2%nat) = SP - 32) by (cbn [base_val]; exact (cp_E2 regs2 HRG)).
assert (E33 : ew (cp_E X regs2) 33 = Z_to_bv 64 (raZ (c_regs X))) by exact (cw_ew_x regs2 (cp_xs X) 0).
assert (E34 : ew (cp_E X regs2) 34 = Z_to_bv 64 (bv_unsigned (getr (c_regs X) 8))) by exact (cw_ew_x regs2 (cp_xs X) 1).
assert (E35 : ew (cp_E X regs2) 35 = Z_to_bv 64 (bv_unsigned (getr (c_regs X) 9))) by exact (cw_ew_x regs2 (cp_xs X) 2).
assert (E36 : ew (cp_E X regs2) 36 = Z_to_bv 64 (bv_unsigned (getr (c_regs X) 18))) by exact (cw_ew_x regs2 (cp_xs X) 3).
unfold region_ok, cp_save. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite U2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val tfibsegs _ _ (SP - 32) 0 8 (SOff 36 0) (bv_unsigned (getr (c_regs X) 18)));
  [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply cp_u64 | cbn; lia |].
  rewrite Z.add_0_r. exact S1.
- apply (chunk_ok_val tfibsegs _ _ (SP - 32) 8 8 (SOff 35 0) (bv_unsigned (getr (c_regs X) 9)));
  [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply cp_u64 | cbn; lia |].
  replace (SP - 32 + 8) with (SP - 24) by lia. exact S2.
- apply (chunk_ok_val tfibsegs _ _ (SP - 32) 16 8 (SOff 34 0) (bv_unsigned (getr (c_regs X) 8)));
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply cp_u64 | cbn; lia |].
  replace (SP - 32 + 16) with (SP - 16) by lia. exact S3.
- apply (chunk_ok_val tfibsegs _ _ (SP - 32) 24 8 (SOff 33 0) (raZ (c_regs X)));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply cp_u64 | cbn; lia |].
  replace (SP - 32 + 24) with (SP - 8) by lia. exact S4.
Qed.
Lemma cp_rs0_ok : forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2, cp_mem B MT X ly2 S2 W2 mem2 md2 -> cp_rg X regs2 ->
  Forall (region_ok tfibsegs (cp_E X regs2) (mrestrict (w_H W2) mem2)) cp_rs0.
Proof.
intros ly2 S2 W2 regs2 mem2 md2 (HJ2 & _ & _ & _ & _ & _ & HSL) HRG.
pose proof HJ2 as (HAR2 & _).
apply Forall_cons; [exact (cp_save_ok W2 regs2 mem2 HSL HRG)|].
pose proof (cw_regs_ok B TL LAWS 0 (cp_xs X) ly2 S2 W2 regs2 mem2 md2 HAR2 ltac:(lia)
  ltac:(unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs2 2)); lia) ltac:(intros a Ha; lia)) as HR.
unfold cw_regs in HR. apply Forall_inv_tail in HR. exact HR.
Qed.
Lemma cp_pers_ok : forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2, cp_mem B MT X ly2 S2 W2 mem2 md2 ->
  Forall (region_ok tfibsegs (cp_E X regs2) (mrestrict (w_H W2) mem2))
    [cpg_img_region CB_PERS 48; cpg_shadow_region CB_PERS 48].
Proof.
intros ly2 S2 W2 regs2 mem2 md2 (HJ2 & _ & _ & _ & _ & KT & _).
pose proof HJ2 as (HAR2 & _).
pose proof HOK as (_ & HRO & HF). unfold CP_ROWS in HF.
pose proof (Forall_inv HF) as (Hro & _). cbn [fst snd] in Hro.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (cpg_img_region_ok B CB_RLO CB_RHI _ W2 mem2 CB_PERS 48).
  + exact (cp_arodata_kept B _ _ _ _ _ _ _ _ _ KT HRO).
  + intros a Ha. replace a with (CB_PERS + (a - CB_PERS)) by lia. apply Hro. lia.
  + intros a Ha. apply (proj1 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, CB_PERS in *; lia))).
  + intros a Ha. apply (proj2 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, CB_PERS in *; lia))).
  + vm_compute. reflexivity.
  + unfold CB_PERS; lia.
  + lia.
  + unfold CB_PERS; lia.
- apply (cpg_shadow_region_ok B _ W2 mem2 ly2 S2 md2 CODEC_GLOBS CB_PERS 48 GM cg_PERS HAR2).
  + apply cp_E32.
  + unfold CB_PERS; lia.
  + unfold CB_PERS; lia.
Qed.
Lemma cp_rs0_disj : forall regs2, cp_rg X regs2 -> pairwise_disjoint (cp_E X regs2) cp_rs0.
Proof.
intros regs2 HRG. destruct cp_sp as (H46 & H47 & _).
assert (U2 : base_val (cp_E X regs2) (Some 2%nat) = SP - 32) by (cbn [base_val]; exact (cp_E2 regs2 HRG)).
apply pairwise_disjoint_of_extents.
change cp_rs0 with ltac:(let v := eval vm_compute in cp_rs0 in exact v).
unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2. cbn [base_val].
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
Qed.
Lemma cp_rs1_disj : forall regs2, cp_rg X regs2 -> pairwise_disjoint (cp_E X regs2) cp_rs1.
Proof.
intros regs2 HRG. destruct cp_sp as (H46 & H47 & _).
assert (U2 : base_val (cp_E X regs2) (Some 2%nat) = SP - 32) by (cbn [base_val]; exact (cp_E2 regs2 HRG)).
assert (U32 : base_val (cp_E X regs2) (Some 32%nat) = SB)
  by (cbn [base_val]; rewrite cp_E32; apply unsigned_lit_small; unfold SB; lia).
apply pairwise_disjoint_of_extents.
change cp_rs1 with ltac:(let v := eval vm_compute in cp_rs1 in exact v).
unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U32. cbn [base_val].
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, SB. cbn [fst snd]. repeat split; lia.
Qed.
(* the start state at a cut, from the regions rs (cp_rs0 or cp_rs1) *)
Lemma cp_start : forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 pc pins rs,
  cp_mem B MT X ly2 S2 W2 mem2 md2 -> cp_rg X regs2 ->
  Forall (fun p => fst p <> 0%bv /\ getr regs2 (fst p) = sv_denot (cp_E X regs2) (snd p)) pins ->
  regions_wf rs = true -> Forall (region_ok tfibsegs (cp_E X regs2) (mrestrict (w_H W2) mem2)) rs ->
  pairwise_disjoint (cp_E X regs2) rs ->
  st_ok tfibsegs (cp_E X regs2) (mkSS pc (cp_pin pins) rs None (mkFacts cw_atoms [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros ly2 S2 W2 regs2 mem2 md2 pc pins rs HM HRG Hp Hwf Hrs Hpd.
destruct cp_sp as (H46 & H47 & Hal & _).
pose proof (cp_E2 regs2 HRG) as U2. pose proof (cp_E32 regs2) as E32.
rewrite restrict_mkst_fx. unfold cp_E in *. apply (entry_st_ok_full tfibsegs).
- apply cp_pin_ok; [apply regs_ok_Ereg | exact Hp].
- exact Hwf.
- exact Hrs.
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms cw_atoms app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, E32, unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  split; [split; [lia | split; [rewrite Zminus_mod, Hal; reflexivity | lia]]|].
  split; [split; [unfold SB; lia | split; [reflexivity | lia]] | exact I].
Qed.
Lemma cp_start0 : forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 pc pins,
  cp_mem B MT X ly2 S2 W2 mem2 md2 -> cp_rg X regs2 ->
  Forall (fun p => fst p <> 0%bv /\ getr regs2 (fst p) = sv_denot (cp_E X regs2) (snd p)) pins ->
  st_ok tfibsegs (cp_E X regs2) (mkSS pc (cp_pin pins) cp_rs0 None (mkFacts cw_atoms [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros ly2 S2 W2 regs2 mem2 md2 pc pins HM HRG Hp.
apply (cp_start ly2 S2 W2 regs2 mem2 md2 pc pins cp_rs0 HM HRG Hp); [vm_compute; reflexivity | | ].
- exact (cp_rs0_ok ly2 S2 W2 regs2 mem2 md2 HM HRG).
- exact (cp_rs0_disj regs2 HRG).
Qed.
Lemma cp_start1 : forall ly2 S2 (W2 : world tfibsegs) regs2 mem2 md2 pc pins,
  cp_mem B MT X ly2 S2 W2 mem2 md2 -> cp_rg X regs2 ->
  Forall (fun p => fst p <> 0%bv /\ getr regs2 (fst p) = sv_denot (cp_E X regs2) (snd p)) pins ->
  st_ok tfibsegs (cp_E X regs2) (mkSS pc (cp_pin pins) cp_rs1 None (mkFacts cw_atoms [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros ly2 S2 W2 regs2 mem2 md2 pc pins HM HRG Hp.
apply (cp_start ly2 S2 W2 regs2 mem2 md2 pc pins cp_rs1 HM HRG Hp); [vm_compute; reflexivity | | ].
- unfold cp_rs1. apply Forall_app. split; [exact (cp_rs0_ok ly2 S2 W2 regs2 mem2 md2 HM HRG)|].
  exact (cp_pers_ok ly2 S2 W2 regs2 mem2 md2 HM).
- exact (cp_rs1_disj regs2 HRG).
Qed.

(* ================================ a run that writes nothing ================================ *)
Lemma cp_ro_view : forall E rs (H : word -> bool) (m m' : word -> option byte),
  (forall a, in_wrange E rs a -> False) -> frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' Hw HF a Ha.
exact (cw_kept_run (fun _ => False) E rs H m m m' (fun x _ _ => eq_refl) HF (fun x Hx => Hw x Hx) a Ha (fun f => f)).
Qed.
Lemma cp_mem_run : forall ly2 S2 (W2 : world tfibsegs) m m' md md',
  cp_mem B MT X ly2 S2 W2 m md ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W2) m' a = aview tfibsegs (w_H W2) m a) ->
  mem_grows (mrestrict (w_H W2) m) (mrestrict (w_H W2) m') ->
  cp_jr B X ly2 S2 W2 m' md' -> same_io md md' ->
  cp_mem B MT X ly2 S2 W2 m' md'.
Proof.
intros ly2 S2 W2 m m' md md' (HJ & Hfr & Hpm & Hio & Hml & KT & S1 & S2' & S3 & S4) Hav HG HJ' Hio'.
destruct (cp_ok_facts B X HOK) as (HAR & Hce & _).
destruct cp_sp as (H46 & H47 & _).
assert (KV : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W2) m) a n v -> val_mem tfibsegs (mrestrict (w_H W2) m') a n v).
{ intros a n v Ha Hn Hv. apply (cw_val_mem_kept (w_H W2) (w_H W2) m m'); [|exact Hv]. intros x Hx. apply Hav. lia. }
split; [exact HJ'|]. split; [exact Hfr|]. split; [exact Hpm|]. split; [exact (same_io_trans _ _ _ Hio Hio')|].
split; [exact Hml|].
split.
{ apply (cw_kept_step B LAWS TB_check_pers (c_lyc X) (c_Sc X) (c_W X) (c_memc X) (c_mdc X) W2 m m' SP cno_wr
    (fun _ => False) Hce HAR KT).
  - intros a Ha _. exact (Hav a Ha).
  - intros a [].
  - intros a Hp. exact (apresent_grows (w_H W2) m m' a HG Hp). }
split; [apply KV; [lia | cbn; lia | exact S1]|].
split; [apply KV; [lia | cbn; lia | exact S2']|].
split; [apply KV; [lia | cbn; lia | exact S3]|].
apply KV; [lia | cbn; lia | exact S4].
Qed.
(* the registers the walk relies on, from the engine's state: each the atom of its own register (s2: atom 32) *)
Definition cp_rg_chk (sr : list sv) : bool :=
forallb (fun z => sv_eqb (sr_get sr (Z_to_bv 5 z)) (SOff (Z.to_nat z) 0)) [2; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] &&
sv_eqb (sr_get sr (Z_to_bv 5 18)) (SOff 32 0).
Lemma cp_rg_run : forall regs2 E' ss (H : word -> bool) ms,
  cp_rg X regs2 -> st_ok tfibsegs E' ss (restrict H ms) ->
  (forall n, (n < 37)%nat -> ew E' n = ew (cp_E X regs2) n) ->
  cp_rg_chk (ss_regs ss) = true -> cp_rg X (ms_regs ms).
Proof.
intros regs2 E' ss H ms (R2 & R3 & R4 & R18 & R19) HS HA Hc.
unfold cp_rg_chk in Hc. apply andb_prop in Hc as [Hc Hc18].
assert (Hz : forall z, In z [2; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 z) = getr regs2 (Z_to_bv 5 z)).
{ intros z Hz. pose proof (proj1 (forallb_forall _ _) Hc z Hz) as Hb. cbv beta in Hb.
  assert (Hzr : 2 <= z <= 27) by (cbn in Hz; lia).
  rewrite (cp_reg_atom E' ss H ms _ (Z.to_nat z) (cp_E X regs2) HS Hb ltac:(lia) HA).
  apply cp_E_reg. rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
split; [rewrite <- cp_r2, (Hz 2 ltac:(cbn; tauto)), cp_r2; exact R2|].
split; [rewrite <- cp_r3, (Hz 3 ltac:(cbn; tauto)), cp_r3; exact R3|].
split; [rewrite <- cp_r4, (Hz 4 ltac:(cbn; tauto)), cp_r4; exact R4|].
split; [rewrite <- cp_r18, (cp_reg_atom E' ss H ms _ 32 (cp_E X regs2) HS Hc18 ltac:(lia) HA), cp_E32; reflexivity|].
intros r Hr. rewrite <- (R19 r Hr). apply Hz.
assert (r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc9 by lia.
cbn [In]. lia.
Qed.

(* ================================ the calls ================================ *)
(* a callee's journal premise at a call made with sp - 32 *)
Lemma cp_entry_call : forall ly2 S2 (W2 : world tfibsegs) regs1 mem2 md2 Tc retpc,
  cp_mem B MT X ly2 S2 W2 mem2 md2 -> cp_rg X regs1 ->
  getr regs1 1 = Z_to_bv 64 retpc -> retpc mod 2 = 0 -> 4096 <= retpc < 2 ^ 64 -> 0 <= Tc -> 32 + Tc <= 8272 ->
  cdc_entry tfibsegs B (c_STK X) (c_sp0 X) (c_FP X) (c_ly X) (c_S X) (c_W0 X) (c_mem0 X) (c_md0 X) (c_own X)
    ly2 S2 W2 mem2 md2 (c_k X) regs1 Tc.
Proof.
intros ly2 S2 W2 regs1 mem2 md2 Tc retpc (HJ & Hfr & Hpm & _) (R2 & R3 & R4 & _) H1 Hev Hr HT HT'.
pose proof HOK as ((_ & _ & _ & Hgp & Htp & _ & _ & _ & Hnev & Hlive) & _).
destruct cp_sp as (H46 & H47 & Hal & _ & Hw1 & Hw2).
assert (Usp : spZ regs1 = SP - 32) by (change (spZ regs1) with (bv_unsigned (getr regs1 2)); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
split; [exact HJ|].
split; [rewrite H1; apply ret_ok_even; rewrite unsigned_lit_small by lia; exact Hev|].
split; [unfold raZ; rewrite H1, unsigned_lit_small by lia; lia|].
split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
split; [rewrite Usp, Zminus_mod, Hal; reflexivity|].
split; [lia|]. split; [lia|].
split; [exact Hnev|].
rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hpm), <- (blocks_bytes_bsum B (c_lyc X) (c_Sc X)). exact Hlive.
Qed.
(* what a call kept, composed into what the walk kept: a caller-journal callee whose blocks are a permutation of
   the call state's (lib/A/Prog/CPgWalkKept.v cw_kept_cj, with Permutation in place of the equality of the
   block lists) *)
Lemma cp_kept_cj : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own3 ly3 S3 W3 mem3 md3 k3
  W4 mem4 T T1 sp sp1 (E E1 : Z -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own3 ly3 S3 W3 mem3 md3 k3 ->
  incl (frames Sc) (frames S3) -> Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) ->
  alloc_ceiling <= sp - T -> sp <= 2 ^ 47 -> sp - T <= sp1 - T1 -> sp1 <= sp ->
  (forall a, E1 a -> (sp - T <= a < sp) \/ (E a /\ ~ in_img tfibsegs a) \/ cw_fresh B lyc Sc a) ->
  tcj_kept tfibsegs B T lyc Sc W memc W3 mem3 sp E ->
  tcj_kept tfibsegs B T1 ly3 S3 W3 mem3 W4 mem4 sp1 E1 ->
  tcj_kept tfibsegs B T lyc Sc W memc W4 mem4 sp E.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own3 ly3 S3 W3 mem3 md3 k3 W4 mem4 T T1 sp sp1 E E1
  HJ HJ3 Hfr Hbl Hce H47 Hw1 Hw2 HE1 (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6).
pose proof HJ as (HAR & Hly & _). pose proof HJ3 as (_ & Hly3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Efr : forall cid pos, frame_addr ly3 cid pos = frame_addr lyc cid pos).
{ intros cid pos. unfold frame_addr.
  destruct Hly as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  rewrite EF, EF3. reflexivity. }
split.
{ intros a Ha Hw HE. rewrite (L1 a Ha).
  - exact (K1 a Ha Hw HE).
  - intros H. apply Hw. clear - H Hw1 Hw2. lia.
  - intros H1. destruct (HE1 a H1) as [Hx | [(Hx & _) | (Hx & _)]]; [exact (Hw Hx) | exact (HE Hx) | clear - Ha Hx; lia]. }
split.
{ intros bb m i Hin Hi HE.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HAR Hin) as (_ & H4096 & Hceil & _).
  rewrite (L2 bb m i (Permutation_in _ (Permutation_sym Hbl) Hin)).
  - exact (K2 bb m i Hin Hi HE).
  - exact Hi.
  - intros H1. destruct (HE1 _ H1) as [Hx | [(Hx & _) | (_ & _ & Hx & _)]];
    [clear - Hx Hce Hceil Hi; lia | exact (HE Hx) | exact (Hx bb m i Hin Hi eq_refl)]. }
split.
{ intros a Him Hns Herr. rewrite (L3 a Him Hns Herr). exact (K3 a Him Hns Herr). }
split.
{ intros cid pos a Hin Hr HE.
  assert (Hr3 : in_zr a (frame_rng ly3 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8))
    by (unfold frame_rng in *; cbn [fst snd] in *; rewrite Efr; exact Hr).
  pose proof (cw_frame_zone_low B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr) as Ha.
  rewrite (L4 cid pos a (Hfr _ Hin) Hr3).
  - exact (K4 cid pos a Hin Hr HE).
  - intros H1. destruct (HE1 _ H1) as [Hx | [(Hx & _) | (_ & _ & _ & Hx)]];
    [clear - Hx Hce Ha; lia | exact (HE Hx) | destruct (Hx cid pos Hin) as (Hf1 & Hf2); destruct Hr as [Hr | Hr]; [exact (Hf1 Hr) | exact (Hf2 Hr)]]. }
split.
{ intros a Ha Hw Hp. apply L5; [exact Ha | intros H; apply Hw; clear - H Hw1 Hw2; lia | exact (K5 a Ha Hw Hp)]. }
intros a Ha. destruct (Z_lt_le_dec a (sp1 - T1)) as [Hl | Hl]; [|destruct (Z_lt_le_dec a sp1) as [Hh | Hh]].
- apply L5; [clear - Ha Hce H47 Hl; lia | clear - Hl; lia | exact (K6 a Ha)].
- apply L6. clear - Hl Hh. lia.
- apply L5; [clear - Ha Hce H47 Hh; lia | clear - Hh; lia | exact (K6 a Ha)].
Qed.
(* the facts at the return of an own callee (window Tc below sp - 32, nothing written outside it) *)
Lemma cp_after_cdc : forall ly1 S1 (W1 : world tfibsegs) regs1 mem1 md1 Tc ly2 S2 W2 regs2 mem2 md2,
  cp_mem B MT X ly1 S1 W1 mem1 md1 -> cp_rg X regs1 -> 0 <= Tc -> 32 + Tc <= 8272 ->
  ajournal tfibsegs B (c_STK X) (c_sp0 X) (c_FP X) (c_ly X) (c_S X) (c_W0 X) (c_mem0 X) (c_md0 X) (c_own X)
    ly2 S2 W2 mem2 md2 (c_k X + EV_CDC) ->
  aregs_preserved regs1 regs2 -> frames S2 = frames S1 -> Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) ->
  same_io md1 md2 -> mo_le MT S1 S2 0 ->
  tcj_kept tfibsegs B Tc ly1 S1 W1 mem1 W2 mem2 (spZ regs1) cno_wr ->
  cp_mem B MT X ly2 S2 W2 mem2 md2 /\ cp_rg X regs2.
Proof.
intros ly1 S1 W1 regs1 mem1 md1 Tc ly2 S2 W2 regs2 mem2 md2 (HJ1 & Hfr1 & Hpm1 & Hio1 & Hml1 & KT1 & S1' & S2' & S3 & S4)
  (R2 & R3 & R4 & R18 & R19) HT HT' HJ2 HP Hfr2 Hpm2 Hio2 Hml2 KT2.
destruct (cp_ok_facts B X HOK) as (HAR & Hce & _).
destruct cp_sp as (H46 & H47 & Hal & _).
pose proof HOK as ((HJ0 & _) & _).
assert (Usp : spZ regs1 = SP - 32) by (change (spZ regs1) with (bv_unsigned (getr regs1 2)); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
rewrite Usp in KT2. unfold EV_CDC in HJ2. rewrite Z.add_0_r in HJ2.
destruct KT2 as (L1 & L2 & L3 & L4 & L5 & L6).
assert (KV : forall a n v, SP - 32 <= a -> a + Z.of_nat n <= SP ->
  val_mem tfibsegs (mrestrict (w_H W1) mem1) a n v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v).
{ intros a n v Ha Hn Hv. apply (cw_val_mem_kept (w_H W1) (w_H W2) mem1 mem2); [|exact Hv]. intros x Hx.
  apply L1; [rewrite cp_T in Hce; lia | lia | intros []]. }
split.
- split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr1|]. split; [exact (Permutation_trans Hpm2 Hpm1)|].
  split; [exact (same_io_trans _ _ _ Hio1 Hio2)|].
  split; [exact (mle_station MT (c_Sc X) S1 S2 0 0 MTL Hml1 Hml2)|].
  split.
  + apply (cp_kept_cj (c_STK X) (c_sp0 X) (c_FP X) (c_ly X) (c_S X) (c_W0 X) (c_mem0 X) (c_md0 X) (c_own X)
      (c_lyc X) (c_Sc X) (c_W X) (c_memc X) (c_mdc X) (c_k X) (c_own X) ly1 S1 W1 mem1 md1 (c_k X) W2 mem2
      TB_check_pers Tc SP (SP - 32) cno_wr cno_wr HJ0 HJ1).
    * rewrite Hfr1. apply incl_refl.
    * exact Hpm1.
    * exact Hce.
    * exact H47.
    * rewrite cp_T. lia.
    * lia.
    * intros a [].
    * exact KT1.
    * split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5 | exact L6].
  + split; [apply KV; [lia | cbn; lia | exact S1']|].
    split; [apply KV; [lia | cbn; lia | exact S2']|].
    split; [apply KV; [lia | cbn; lia | exact S3]|].
    apply KV; [lia | cbn; lia | exact S4].
- assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HP.
  split; [rewrite <- cp_r2, (P 2 ltac:(unfold acallee_saved; lia)), cp_r2; exact R2|].
  split; [rewrite <- cp_r3, (P 3 ltac:(unfold acallee_saved; lia)), cp_r3; exact R3|].
  split; [rewrite <- cp_r4, (P 4 ltac:(unfold acallee_saved; lia)), cp_r4; exact R4|].
  split; [rewrite <- cp_r18, (P 18 ltac:(unfold acallee_saved; lia)), cp_r18; exact R18|].
  intros r Hr. rewrite (P r ltac:(unfold acallee_saved; lia)). exact (R19 r Hr).
Qed.
(* the facts at the return of the strcmp wrapper (window 2 * ESTACK below sp - 32) *)
Lemma cp_after_str : forall ly1 S1 (W1 : world tfibsegs) regs1 mem1 md1 regs2 mem2 md2,
  cp_mem B MT X ly1 S1 W1 mem1 md1 -> cp_rg X regs1 ->
  cp_jr B X ly1 S1 W1 mem2 md2 -> aregs_preserved regs1 regs2 -> same_but_materialized md1 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (SP - 32 - 2 * ESTACK <= a < SP - 32) ->
     aview tfibsegs (w_H W1) mem2 a = aview tfibsegs (w_H W1) mem1 a) ->
  (forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) mem2 a) ->
  cp_mem B MT X ly1 S1 W1 mem2 md2 /\ cp_rg X regs2.
Proof.
intros ly1 S1 W1 regs1 mem1 md1 regs2 mem2 md2 (HJ1 & Hfr1 & Hpm1 & Hio1 & Hml1 & KT1 & S1' & S2' & S3 & S4)
  (R2 & R3 & R4 & R18 & R19) HJ2 HP Hsm Hfr Hpr.
destruct (cp_ok_facts B X HOK) as (HAR & Hce & _).
destruct cp_sp as (H46 & H47 & Hal & _).
assert (KV : forall a n v, SP - 32 <= a -> a + Z.of_nat n <= SP ->
  val_mem tfibsegs (mrestrict (w_H W1) mem1) a n v -> val_mem tfibsegs (mrestrict (w_H W1) mem2) a n v).
{ intros a n v Ha Hn Hv. apply (cw_val_mem_kept (w_H W1) (w_H W1) mem1 mem2); [|exact Hv]. intros x Hx.
  apply Hfr; [lia | lia]. }
split.
- split; [exact HJ2|]. split; [exact Hfr1|]. split; [exact Hpm1|].
  split; [apply (same_io_trans _ _ _ Hio1); unfold same_but_materialized in Hsm; rewrite Hsm; apply cw_same_io_wvb|].
  split; [exact Hml1|].
  split.
  + apply (cw_kept_step B LAWS TB_check_pers (c_lyc X) (c_Sc X) (c_W X) (c_memc X) (c_mdc X) W1 mem1 mem2 SP cno_wr
      (fun a => SP - 32 - 2 * ESTACK <= a < SP - 32) Hce HAR KT1).
    * intros a Ha Hx. exact (Hfr a Ha Hx).
    * intros a Ha. left. unfold ESTACK in Ha. rewrite cp_T. lia.
    * exact Hpr.
  + split; [apply KV; [lia | cbn; lia | exact S1']|].
    split; [apply KV; [lia | cbn; lia | exact S2']|].
    split; [apply KV; [lia | cbn; lia | exact S3]|].
    apply KV; [lia | cbn; lia | exact S4].
- assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HP.
  split; [rewrite <- cp_r2, (P 2 ltac:(unfold acallee_saved; lia)), cp_r2; exact R2|].
  split; [rewrite <- cp_r3, (P 3 ltac:(unfold acallee_saved; lia)), cp_r3; exact R3|].
  split; [rewrite <- cp_r4, (P 4 ltac:(unfold acallee_saved; lia)), cp_r4; exact R4|].
  split; [rewrite <- cp_r18, (P 18 ltac:(unfold acallee_saved; lia)), cp_r18; exact R18|].
  intros r Hr. rewrite (P r ltac:(unfold acallee_saved; lia)). exact (R19 r Hr).
Qed.

(* ================================ the rows at a later state ================================ *)
(* a row's crd_ok at a call made from a cut: the bytes from the read-only data, the shadow from cimg_usable *)
Lemma cp_crd_cur : forall ly2 S2 (W2 : world tfibsegs) mem2 md2 sp' T' q n,
  cp_mem B MT X ly2 S2 W2 mem2 md2 -> In (q, n) CP_ROWS -> SP - 8272 <= sp' - T' ->
  crd_ok tfibsegs W2 mem2 sp' T' q n.
Proof.
intros ly2 S2 W2 mem2 md2 sp' T' q n (HJ2 & _ & _ & _ & _ & KT & _) Hin Hw.
pose proof HJ2 as (HAR2 & _).
pose proof HOK as (_ & HRO & HF).
pose proof (proj1 (Forall_forall _ _) HF (q, n) Hin) as (Hro & Hq0 & Hn0 & H63 & Ham & Hcw & Himg & Hus).
cbn [fst snd] in *.
pose proof (cp_arodata_kept B _ _ _ _ _ _ _ _ _ KT HRO) as HRO2.
destruct (Hus ly2 S2 W2 mem2 md2 HAR2) as (Hra & Hhv).
destruct (cp_row_facts q n Hin) as (Hs & _ & _ & _ & H9e & _).
destruct cp_sp as (H46 & _).
split; [exact Hq0|]. split; [exact H63|].
split.
{ intros a Ha. replace a with (q + (a - q)) by lia.
  rewrite (cpw_row_view B CB_RLO CB_RHI W2 mem2 CP_ROWS q n (a - q) HRO2 (cp_rows_free_all B TL RF) Hin Hro ltac:(lia)).
  assert (Hk : In (Z.to_nat (a - q)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Hs _ Hk) as Hb. cbv beta in Hb.
  rewrite Z2Nat.id in Hb by lia.
  destruct (img_byte tfibsegs (q + (a - q))); [discriminate | discriminate Hb]. }
split; [exact Hra|]. split; [exact Hhv|]. split; [exact Ham|].
unfold coff_win in *. lia.
Qed.
(* the callee's cimg_rd at a call made from a cut *)
Lemma cp_cimg_cur : forall ly2 S2 (W2 : world tfibsegs) mem2 md2 sp' T',
  cp_mem B MT X ly2 S2 W2 mem2 md2 -> SP - 8272 <= sp' - T' ->
  cimg_rd tfibsegs B CB_RLO CB_RHI W2 mem2 sp' T' CP_ROWS.
Proof.
intros ly2 S2 W2 mem2 md2 sp' T' (HJ2 & _ & _ & _ & _ & KT & _) Hw.
pose proof HOK as (_ & HRO & HF).
destruct cp_sp as (H46 & _).
split; [exact (cp_arodata_kept B _ _ _ _ _ _ _ _ _ KT HRO)|].
apply Forall_forall. intros [q n] Hin.
pose proof (proj1 (Forall_forall _ _) HF (q, n) Hin) as (Hro & Hq0 & Hn0 & H63 & Ham & Hcw & Himg & Hus).
cbn [fst snd] in *.
destruct (cp_row_facts q n Hin) as (_ & _ & _ & _ & H9e & _).
split; [exact Hro|]. split; [exact Hq0|]. split; [exact Hn0|]. split; [exact H63|]. split; [exact Ham|].
split; [unfold coff_win in *; lia|]. split; [exact Himg | exact Hus].
Qed.

(* ================================ the calls ================================ *)
Lemma cp_call_po : forall ly1 S1 (W1 : world tfibsegs) regs1 mem1 md1 d retpc (Rg : bvmap 5 word -> Prop),
  cdcU_pers_of_specX tfibsegs B MT B_PERS_OF CB_PERS ->
  cp_mem B MT X ly1 S1 W1 mem1 md1 -> cp_rg X regs1 ->
  getr regs1 10 = w64 d -> 0 <= d < 2 ^ 64 ->
  getr regs1 1 = Z_to_bv 64 retpc -> retpc mod 2 = 0 -> 4096 <= retpc < 2 ^ 64 ->
  (forall regs2, aregs_preserved regs1 regs2 -> getr regs2 10 = w64 (pers_ofA CB_PERS d) -> Rg regs2) ->
  cp_rest B MT X retpc Rg ->
  SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 B_PERS_OF) mem1 (seg_rom tfibsegs)) md1) (cp_post B MT X).
Proof.
intros ly1 S1 W1 regs1 mem1 md1 d retpc Rg POF HM HRG H10 Hd H1 Hev Hr HRg NEXT.
pose proof (cp_entry_call ly1 S1 W1 regs1 mem1 md1 TB_pers_of retpc HM HRG H1 Hev Hr
  ltac:(unfold TB_pers_of; lia) ltac:(unfold TB_pers_of; lia)) as HEc.
eapply SRr_bind; [exact (POF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d HEc H10 Hd)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hfr & Hpm & Hio & Hml & KT & HR).
destruct (cp_after_cdc ly1 S1 W1 regs1 mem1 md1 TB_pers_of ly2 S2 W2 regs2 mem2 md2 HM HRG
  ltac:(unfold TB_pers_of; lia) ltac:(unfold TB_pers_of; lia) HJ2 HP Hfr Hpm Hio Hml KT) as (HM2 & HRG2).
apply NEXT. exists ly2, S2, regs2, mem2, md2.
split; [rewrite H1; reflexivity|]. split; [exact HM2|]. split; [exact HRG2|]. exact (HRg regs2 HP HR).
Qed.
Lemma cp_call_fn : forall ly1 S1 (W1 : world tfibsegs) regs1 mem1 md1 q n retpc (Rg : bvmap 5 word -> Prop),
  cdcU_from_name_specX tfibsegs B MT CB_RLO CB_RHI CB_PERS CB_ROSTRS B_FROM_NAME ->
  cp_mem B MT X ly1 S1 W1 mem1 md1 -> cp_rg X regs1 ->
  getr regs1 10 = w64 q -> In (q, n) CB_ROSTRS -> existsb (Z.eqb 0) (cpw_img_list q n) = true ->
  getr regs1 1 = Z_to_bv 64 retpc -> retpc mod 2 = 0 -> 4096 <= retpc < 2 ^ 64 ->
  (forall regs2, aregs_preserved regs1 regs2 ->
     getr regs2 10 = w64 (from_name_resA CB_PERS (cpw_img_list q n)) -> Rg regs2) ->
  cp_rest B MT X retpc Rg ->
  SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 B_FROM_NAME) mem1 (seg_rom tfibsegs)) md1) (cp_post B MT X).
Proof.
intros ly1 S1 W1 regs1 mem1 md1 q n retpc Rg FN HM HRG H10 Hin H0 H1 Hev Hr HRg NEXT.
assert (HinP : In (q, n) CP_ROWS) by (right; exact Hin).
pose proof HM as (_ & _ & _ & _ & _ & KT & _).
pose proof HOK as (_ & HRO & HF).
pose proof (proj1 (Forall_forall _ _) HF (q, n) HinP) as (Hro & _). cbn [fst snd] in Hro.
destruct (cp_row_facts q n HinP) as (Hs & Hn0 & Hlo & _ & H9e & _).
destruct cp_sp as (H46 & H47 & _).
pose proof HRG as (R2 & _).
assert (Usp : spZ regs1 = SP - 32)
  by (change (spZ regs1) with (bv_unsigned (getr regs1 2)); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
pose proof (cp_entry_call ly1 S1 W1 regs1 mem1 md1 TB_from_name retpc HM HRG H1 Hev Hr
  ltac:(unfold TB_from_name, ESTACK; lia) ltac:(unfold TB_from_name, ESTACK; lia)) as HEc.
assert (Hcs : cstr_rd tfibsegs W1 mem1 (spZ regs1) TB_from_name q (cpw_img_list q n)).
{ split; [unfold IMG_LO in Hlo; lia|].
  split; [exact (cpw_row_garr8 B CB_RLO CB_RHI W1 mem1 CP_ROWS q n (cp_arodata_kept B _ _ _ _ _ _ _ _ _ KT HRO)
    (cp_rows_free_all B TL RF) HinP Hro Hs ltac:(lia))|].
  split; [exact (cp_in0 _ H0)|].
  rewrite cpw_img_list_length by lia.
  apply (cp_crd_cur ly1 S1 W1 mem1 md1 _ _ q n HM HinP). rewrite Usp. unfold TB_from_name, ESTACK. lia. }
assert (Hci : cimg_rd tfibsegs B CB_RLO CB_RHI W1 mem1 (spZ regs1) TB_from_name CP_ROWS)
  by (apply (cp_cimg_cur ly1 S1 W1 mem1 md1 _ _ HM); rewrite Usp; unfold TB_from_name, ESTACK; lia).
eapply SRr_bind; [exact (FN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q (cpw_img_list q n) HEc H10 Hcs Hci)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hfr & Hpm & Hio & Hml & KT2 & HR).
destruct (cp_after_cdc ly1 S1 W1 regs1 mem1 md1 TB_from_name ly2 S2 W2 regs2 mem2 md2 HM HRG
  ltac:(unfold TB_from_name, ESTACK; lia) ltac:(unfold TB_from_name, ESTACK; lia) HJ2 HP Hfr Hpm Hio Hml KT2) as (HM2 & HRG2).
apply NEXT. exists ly2, S2, regs2, mem2, md2.
split; [rewrite H1; reflexivity|]. split; [exact HM2|]. split; [exact HRG2|]. exact (HRg regs2 HP HR).
Qed.
Lemma cp_call_str : forall ly1 S1 (W1 : world tfibsegs) regs1 mem1 md1 x y nx ny sx sy retpc (Rg : bvmap 5 word -> Prop),
  astrcmp_realizes tfibsegs B B_STRCMP ->
  cp_mem B MT X ly1 S1 W1 mem1 md1 -> cp_rg X regs1 ->
  getr regs1 10 = w64 x -> getr regs1 11 = w64 y ->
  In (x, nx) CP_ROWS -> In (y, ny) CP_ROWS -> Z.of_nat (length sx) + 1 = nx -> Z.of_nat (length sy) + 1 = ny ->
  cw_img_cstr x sx = true -> cw_img_cstr y sy = true ->
  getr regs1 1 = Z_to_bv 64 retpc -> retpc mod 2 = 0 -> 4096 <= retpc < 2 ^ 64 ->
  (forall regs2, aregs_preserved regs1 regs2 -> getr regs2 10 = w64 (cw_strcmpZ sx sy) -> Rg regs2) ->
  cp_rest B MT X retpc Rg ->
  SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 B_STRCMP) mem1 (seg_rom tfibsegs)) md1) (cp_post B MT X).
Proof.
intros ly1 S1 W1 regs1 mem1 md1 x y nx ny sx sy retpc Rg STR HM HRG H10 H11 Hinx Hiny Hlx Hly Hcx Hcy H1 Hev Hr HRg NEXT.
pose proof HM as (HJ1 & _ & _ & _ & _ & KT & _).
pose proof HOK as ((HJ0 & _ & _ & Hgp & Htp & _) & HRO & HF).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp016 & _) & _).
pose proof (cp_arodata_kept B _ _ _ _ _ _ _ _ _ KT HRO) as HRO1.
pose proof (proj1 (Forall_forall _ _) HF (x, nx) Hinx) as (Hrox & _).
pose proof (proj1 (Forall_forall _ _) HF (y, ny) Hiny) as (Hroy & _). cbn [fst snd] in Hrox, Hroy.
destruct (cp_row_facts x nx Hinx) as (_ & Hnx & Hlox & _ & H9x & _).
destruct (cp_row_facts y ny Hiny) as (_ & Hny & Hloy & _ & H9y & _).
destruct cp_sp as (H46 & H47 & Hal & _ & Hw1 & Hw2).
pose proof HRG as (R2 & R3 & R4 & _).
assert (Usp : spZ regs1 = SP - 32)
  by (change (spZ regs1) with (bv_unsigned (getr regs1 2)); rewrite R2; unfold w64; apply unsigned_lit_small; lia).
set (o := SP - 32 - c_sp0 X).
assert (Ho : c_sp0 X + o = SP - 32) by (unfold o; lia).
assert (Hom : o mod 16 = 0) by (unfold o; rewrite Zminus_mod, (Zminus_mod SP 32 16), Hal, Hsp016; reflexivity).
eapply SRr_bind.
{ apply (cw_strcmp_cstr_at B LAWS B_STRCMP STR W1 regs1 mem1 (c_STK X) (c_sp0 X) (c_FP X) (c_ly X) (c_S X) (c_W0 X)
    (c_mem0 X) (c_md0 X) (c_own X) ly1 S1 md1 (c_k X) x y sx sy o (Z_to_bv 64 retpc) HJ1 H10 H11).
  - unfold IMG_LO in Hlox. lia.
  - unfold IMG_LO in Hloy. lia.
  - rewrite Usp. lia.
  - exact Hom.
  - unfold o. lia.
  - unfold o, ESTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact H1.
  - apply ret_ok_even. rewrite unsigned_lit_small by lia. exact Hev.
  - left. rewrite Hlx. unfold IMG_LO in Hlox. lia.
  - exact (cw_cstr_row B CB_RLO CB_RHI W1 mem1 CP_ROWS x nx sx HRO1 (cp_rows_free_all B TL RF) Hinx Hrox ltac:(rewrite Hlx; lia) Hcx).
  - exact (cw_cstr_row B CB_RLO CB_RHI W1 mem1 CP_ROWS y ny sy HRO1 (cp_rows_free_all B TL RF) Hiny Hroy ltac:(rewrite Hly; lia) Hcy).
  - rewrite Hlx, Ho. apply (cp_crd_cur ly1 S1 W1 mem1 md1 _ _ x nx HM Hinx). unfold ESTACK. lia.
  - rewrite Hly, Ho. apply (cp_crd_cur ly1 S1 W1 mem1 md1 _ _ y ny HM Hiny). unfold ESTACK. lia. }
intros W2 cf _ (HW & regs2 & mem2 & md2 & -> & HJ2 & HP & Hsm & Hv & Hfr & Hpr). subst W2.
rewrite Ho in Hfr.
destruct (cp_after_str ly1 S1 W1 regs1 mem1 md1 regs2 mem2 md2 HM HRG HJ2 HP Hsm Hfr Hpr) as (HM2 & HRG2).
apply NEXT. exists ly1, S1, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HM2|]. split; [exact HRG2|]. exact (HRg regs2 HP Hv).
Qed.

(* ================================ the return ================================ *)
Lemma cp_r1 : Z_to_bv 5 1 = (1%bv : bv 5). Proof. apply bv_eq. reflexivity. Qed.
Lemma cp_r8 : Z_to_bv 5 8 = (8%bv : bv 5). Proof. apply bv_eq. reflexivity. Qed.
Lemma cp_r9 : Z_to_bv 5 9 = (9%bv : bv 5). Proof. apply bv_eq. reflexivity. Qed.
(* the engine's registers at the `ret`: ra, s0, s1, s2 the save slots' atoms, sp back, the others their own *)
Definition cp_fin_chk (sr : list sv) : bool :=
sv_eqb (sr_get sr (Z_to_bv 5 1)) (SOff 33 0) && sv_eqb (sr_get sr (Z_to_bv 5 2)) (SOff 2 32) &&
sv_eqb (sr_get sr (Z_to_bv 5 8)) (SOff 34 0) && sv_eqb (sr_get sr (Z_to_bv 5 9)) (SOff 35 0) &&
sv_eqb (sr_get sr (Z_to_bv 5 18)) (SOff 36 0) &&
forallb (fun z => sv_eqb (sr_get sr (Z_to_bv 5 z)) (SOff (Z.to_nat z) 0)) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma cp_fin_regs : forall regs2 E' ss (H : word -> bool) ms,
  cp_rg X regs2 -> st_ok tfibsegs E' ss (restrict H ms) ->
  (forall n, (n < 37)%nat -> ew E' n = ew (cp_E X regs2) n) ->
  cp_fin_chk (ss_regs ss) = true ->
  aregs_preserved (c_regs X) (ms_regs ms) /\ getr (ms_regs ms) 1 = getr (c_regs X) 1.
Proof.
intros regs2 E' ss H ms (R2 & R3 & R4 & R18 & R19) HS HA Hc.
destruct cp_sp as (H46 & H47 & _).
assert (E33 : ew (cp_E X regs2) 33 = Z_to_bv 64 (raZ (c_regs X))) by exact (cw_ew_x regs2 (cp_xs X) 0).
assert (E34 : ew (cp_E X regs2) 34 = Z_to_bv 64 (bv_unsigned (getr (c_regs X) 8))) by exact (cw_ew_x regs2 (cp_xs X) 1).
assert (E35 : ew (cp_E X regs2) 35 = Z_to_bv 64 (bv_unsigned (getr (c_regs X) 9))) by exact (cw_ew_x regs2 (cp_xs X) 2).
assert (E36 : ew (cp_E X regs2) 36 = Z_to_bv 64 (bv_unsigned (getr (c_regs X) 18))) by exact (cw_ew_x regs2 (cp_xs X) 3).
unfold cp_fin_chk in Hc.
repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?] end.
rename Hc into C1.
match goal with
| H2 : sv_eqb (sr_get _ (Z_to_bv 5 2)) _ = true, H8 : sv_eqb (sr_get _ (Z_to_bv 5 8)) _ = true,
  H9 : sv_eqb (sr_get _ (Z_to_bv 5 9)) _ = true, H18 : sv_eqb (sr_get _ (Z_to_bv 5 18)) _ = true,
  HL : forallb _ _ = true |- _ => rename H2 into C2; rename H8 into C8; rename H9 into C9; rename H18 into C18;
  rename HL into CL end.
assert (Hz : forall z, In z [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 z) = getr regs2 (Z_to_bv 5 z)).
{ intros z Hz. pose proof (proj1 (forallb_forall _ _) CL z Hz) as Hb. cbv beta in Hb.
  assert (Hzr : 3 <= z <= 27) by (cbn in Hz; lia).
  rewrite (cp_reg_atom E' ss H ms _ (Z.to_nat z) (cp_E X regs2) HS Hb ltac:(lia) HA).
  apply cp_E_reg. rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (G1 : getr (ms_regs ms) (Z_to_bv 5 1) = getr (c_regs X) 1).
{ rewrite (cp_reg_atom E' ss H ms _ 33 (cp_E X regs2) HS C1 ltac:(lia) HA).
  rewrite E33. unfold raZ. apply Z_to_bv_bv_unsigned. }
assert (G2 : getr (ms_regs ms) (Z_to_bv 5 2) = getr (c_regs X) 2).
{ rewrite (st_ok_restrict_reg tfibsegs H E' ss ms _ HS), (sv_eqb_eq _ _ C2). cbn [sv_denot].
  rewrite (HA 2%nat ltac:(lia)), (cp_E2 regs2 (conj R2 (conj R3 (conj R4 (conj R18 R19))))).
  replace (SP - 32 + 32) with SP by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
assert (G8 : getr (ms_regs ms) (Z_to_bv 5 8) = getr (c_regs X) 8).
{ rewrite (cp_reg_atom E' ss H ms _ 34 (cp_E X regs2) HS C8 ltac:(lia) HA).
  rewrite E34. apply Z_to_bv_bv_unsigned. }
assert (G9 : getr (ms_regs ms) (Z_to_bv 5 9) = getr (c_regs X) 9).
{ rewrite (cp_reg_atom E' ss H ms _ 35 (cp_E X regs2) HS C9 ltac:(lia) HA).
  rewrite E35. apply Z_to_bv_bv_unsigned. }
assert (G18 : getr (ms_regs ms) (Z_to_bv 5 18) = getr (c_regs X) 18).
{ rewrite (cp_reg_atom E' ss H ms _ 36 (cp_E X regs2) HS C18 ltac:(lia) HA).
  rewrite E36. apply Z_to_bv_bv_unsigned. }
split; [|rewrite <- cp_r1; exact G1].
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
- rewrite G2, cp_r2. reflexivity.
- rewrite (Hz 3 ltac:(cbn; tauto)), cp_r3. exact R3.
- rewrite (Hz 4 ltac:(cbn; tauto)), cp_r4. exact R4.
- rewrite G8, cp_r8. reflexivity.
- rewrite G9, cp_r9. reflexivity.
- destruct (Z.eq_dec r 18) as [-> | Hne]; [rewrite G18, cp_r18; reflexivity|].
  rewrite (Hz r); [exact (R19 r ltac:(lia))|].
  assert (r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc9 by lia.
  cbn [In]. lia.
Qed.
(* the post at the return, from the facts at the last cut and the registers at the `ret` *)
Lemma cp_post_ret : forall ly2 S2 (W2 : world tfibsegs) mem2 md2 regsF mat,
  cp_mem B MT X ly2 S2 W2 mem2 md2 -> aregs_preserved (c_regs X) regsF -> getr regsF 1 = getr (c_regs X) 1 ->
  cp_post B MT X W2 (mkCfg (mkst regsF (v_jalr (getr regsF 1) 0) mem2 (seg_rom tfibsegs))
    (with_vm_backing (m_vm_lazy md2) mat md2)).
Proof.
intros ly2 S2 W2 mem2 md2 regsF mat (HJ & Hfr & Hpm & Hio & Hml & KT & _) HP H1.
pose proof HOK as ((_ & Hra & _) & _).
red. exists ly2, S2, regsF, mem2, (with_vm_backing (m_vm_lazy md2) mat md2).
split; [rewrite H1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
pose proof tfib_segs_low as Hsegs.
split; [unfold EV_CDC; rewrite Z.add_0_r; unfold cp_jr in HJ; eapply ajournal_materialize; eassumption|].
split; [exact HP|]. split; [exact Hfr|]. split; [exact Hpm|].
split; [eapply same_io_trans; [exact Hio | apply cw_same_io_wvb]|].
split; [exact Hml|]. split; [exact KT | exact I].
Qed.
(* what a run from a cut keeps of the env *)
Lemma cp_agree : forall E K ws, (37 <= K)%nat -> forall n, (n < 37)%nat -> ew (extK E K ws) n = ew E n.
Proof. intros E K ws HK n Hn. destruct (env_agree_extK E K ws) as [HA _]. apply HA. lia. Qed.

(* ================================ the pins of the cuts ================================ *)
Lemma cp_pin18 : forall regs2, cp_rg X regs2 -> getr regs2 18%bv = sv_denot (cp_E X regs2) (SOff 32 0).
Proof. intros regs2 (_ & _ & _ & R18 & _). rewrite R18. cbn [sv_denot]. rewrite cp_E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma cp_pins1_ok : forall regs2, cp_rg X regs2 -> cp_R1 regs2 ->
  Forall (fun p => fst p <> 0%bv /\ getr regs2 (fst p) = sv_denot (cp_E X regs2) (snd p)) cp_pins1.
Proof.
intros regs2 HRG HR. unfold cp_pins1.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [intros Hc; discriminate Hc|]).
- exact HR.
- exact (cp_pin18 regs2 HRG).
Qed.
Lemma cp_pins2_ok : forall regs2, cp_rg X regs2 -> cp_R2 regs2 ->
  Forall (fun p => fst p <> 0%bv /\ getr regs2 (fst p) = sv_denot (cp_E X regs2) (snd p)) cp_pins2.
Proof.
intros regs2 HRG (H10 & H9). unfold cp_pins2.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [intros Hc; discriminate Hc|]).
- exact H10.
- exact H9.
- exact (cp_pin18 regs2 HRG).
Qed.
Lemma cp_pins_s_ok : forall regs2 a0, cp_rg X regs2 -> cp_Rs a0 regs2 ->
  Forall (fun p => fst p <> 0%bv /\ getr regs2 (fst p) = sv_denot (cp_E X regs2) (snd p)) (cp_pins_s a0).
Proof.
intros regs2 a0 HRG (H10 & H9 & H8). unfold cp_pins_s.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [intros Hc; discriminate Hc|]).
- exact H10.
- exact H9.
- exact H8.
- exact (cp_pin18 regs2 HRG).
Qed.
(* the next cut's registers: s0 and s1 kept by the call, a0 its result *)
Lemma cp_Rs_next : forall regs1 regs2 a v, aregs_preserved regs1 regs2 ->
  getr regs1 9 = w64 CB_PERS -> getr regs1 8 = w64 (CB_PERS + 24) -> getr regs2 10 = w64 a -> a = v -> cp_Rs v regs2.
Proof.
intros regs1 regs2 a v HP H9 H8 H10 Ha. subst a.
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HP.
split; [exact H10|].
split; [rewrite <- cp_r9, (P 9 ltac:(unfold acallee_saved; lia)), cp_r9; exact H9|].
rewrite <- cp_r8, (P 8 ltac:(unfold acallee_saved; lia)), cp_r8; exact H8.
Qed.

(* ================================ the entry segment ================================ *)
(* the save slots, from the save area's chunks after the prologue *)
Lemma cp_slots0 : forall Ev (W2 : world tfibsegs) mem2,
  region_ok tfibsegs Ev (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
    [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
  (forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ev n = getr (c_regs X) r) ->
  cp_slots X W2 mem2.
Proof.
intros Ev W2 mem2 HR HA.
assert (Hb : bv_unsigned (ew Ev 2) = SP) by (rewrite (HA 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
assert (D : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot Ev (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr (c_regs X) r))).
{ intros n r Hn Hr. cbn [sv_denot]. rewrite (HA n r Hn Hr), Z.add_0_r. reflexivity. }
split; [|split; [|split]].
- pose proof (field_of_region Ev _ 2%nat SP _ _ _ _ _ (-32) 8 (SOff 18 0) _ HR Hb ltac:(cbn [In]; tauto)
    (D 18%nat 18%bv ltac:(lia) eq_refl) (cp_u64 _) ltac:(cbn; lia)) as V.
  replace (SP + -32) with (SP - 32) in V by lia. exact V.
- pose proof (field_of_region Ev _ 2%nat SP _ _ _ _ _ (-24) 8 (SOff 9 0) _ HR Hb ltac:(cbn [In]; tauto)
    (D 9%nat 9%bv ltac:(lia) eq_refl) (cp_u64 _) ltac:(cbn; lia)) as V.
  replace (SP + -24) with (SP - 24) in V by lia. exact V.
- pose proof (field_of_region Ev _ 2%nat SP _ _ _ _ _ (-16) 8 (SOff 8 0) _ HR Hb ltac:(cbn [In]; tauto)
    (D 8%nat 8%bv ltac:(lia) eq_refl) (cp_u64 _) ltac:(cbn; lia)) as V.
  replace (SP + -16) with (SP - 16) in V by lia. exact V.
- pose proof (field_of_region Ev _ 2%nat SP _ _ _ _ _ (-8) 8 (SOff 1 0) _ HR Hb ltac:(cbn [In]; tauto)
    (D 1%nat 1%bv ltac:(lia) eq_refl) (cp_u64 _) ltac:(cbn; lia)) as V.
  replace (SP + -8) with (SP - 8) in V by lia. exact V.
Qed.
(* the registers after the prologue: sp - 32, s2 = SB, the others the entry's *)
Definition cp_rg0_chk (sr : list sv) : bool :=
sv_eqb (sr_get sr (Z_to_bv 5 2)) (SOff 2 (-32)) && sv_eqb (sr_get sr (Z_to_bv 5 18)) (SOff 32 0) &&
forallb (fun z => sv_eqb (sr_get sr (Z_to_bv 5 z)) (SOff (Z.to_nat z) 0)) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma cp_rg0 : forall Ev ss (H : word -> bool) ms, st_ok tfibsegs Ev ss (restrict H ms) ->
  (forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ev n = getr (c_regs X) r) ->
  ew Ev 32 = Z_to_bv 64 SB -> cp_rg0_chk (ss_regs ss) = true -> cp_rg X (ms_regs ms).
Proof.
intros Ev ss H ms HS HA H32 Hc.
destruct cp_sp as (H46 & H47 & _).
unfold cp_rg0_chk in Hc. apply andb_prop in Hc as [Hc CL]. apply andb_prop in Hc as [C2 C18].
assert (Hz : forall z, In z [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 z) = getr (c_regs X) (Z_to_bv 5 z)).
{ intros z Hz. pose proof (proj1 (forallb_forall _ _) CL z Hz) as Hb. cbv beta in Hb.
  assert (Hzr : 3 <= z <= 27) by (cbn in Hz; lia).
  rewrite (st_ok_restrict_reg tfibsegs H Ev ss ms _ HS), (sv_eqb_eq _ _ Hb). cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply HA; [lia|].
  rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
split.
{ rewrite <- cp_r2, (st_ok_restrict_reg tfibsegs H Ev ss ms _ HS), (sv_eqb_eq _ _ C2). cbn [sv_denot].
  rewrite (HA 2%nat 2%bv ltac:(lia) eq_refl). reflexivity. }
split; [rewrite <- cp_r3; exact (Hz 3 ltac:(cbn; tauto))|].
split; [rewrite <- cp_r4; exact (Hz 4 ltac:(cbn; tauto))|].
split.
{ rewrite <- cp_r18, (st_ok_restrict_reg tfibsegs H Ev ss ms _ HS), (sv_eqb_eq _ _ C18). cbn [sv_denot].
  rewrite H32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
intros r Hr. apply Hz.
assert (r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) as Hc9 by lia.
cbn [In]. lia.
Qed.
End c.
End b.
