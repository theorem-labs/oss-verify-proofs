(* The IMG_ hypotheses of lib/B/Prog/GrantBContracts.v as PROVED facts of image B, for image B's own instance
   PI_grant (lib/B/Prog/GrantImg.v).

   The step from the image's bytes to the form a contract asks for (garr8 / val_mem over a reader that satisfies
   arodata_okP) is image A's: lib/B/Prog/GrantCloseChk.v, the port of lib/A/Prog/GrantCloseChk.v at a working branch
   af735a950e2 (arodata_garr8 :191, arodata_byte :175, arodata_aview :158, garr8_val_mem :210), with that file's
   two added lemmas arodata_garr8_rom / arodata_aview_tbl_rom, which take the image's bytes from a computation
   (rom_chk over image B's own segments and read-only range) and the two facts about the abstract B as premises:
     ro_free B a n : no byte of [a, a + n) is an owned static of B or a byte of B's errno cell.
   Image A's file folds those two into its check, because it runs at the concrete GrantB; the layer states each
   IMG_ fact for ANY B, so here they stay premises and the closing file discharges them at image B's asyms record
   by the same computation (image A's GrantClose.v:321-392 tbl_obj / row_obj).

   NOT here: IMG_LLVMF_TRACES is not a byte fact (it speaks of as_universe B and as_code B); lib/B/Prog/GrantBClose.v:217
   proves it. IMG_RO_BELOW is a fact about the sink head, not about bytes. The `in_zs B` conjuncts of
   IMG_CTRL_ROW / IMG_CTRL_TMPL and the `In (.., n) GRANT_GLOBS_B` conjuncts are proved here where they are
   computations of image B, and the rest of each definition is left to its own lemma below. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09 YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantRo GrantCloseChk.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantImg GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSweepModel GroupaModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The read-only range of image B, as GrantImg.v's instance fixes it. *)
#[local] Notation SG := grantsegsB0.
#[local] Notation RLO := grant_relro_lo.
#[local] Notation RHI := grant_relro_hi.
(* A value of n bytes, as the byte list garr8_val_mem reads. *)
Definition vbytes (v : Z) (n : nat) : list Z := map (fun k => YO0f.le_byte v n k) (seq 0 n).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the checks of the three regions no lemma checked ------------------------------------------------------
   The control-frame row (B_ROW = object 18 + 240 = 0x9d4d0, 24 bytes, in the read-only-after-relocation range),
   the template TMPL_HEADAMP (0x211c0, 32 bytes) and the two sweep tables (objects 22 / 23). *)
Lemma b_row_check :
  grant_obj 18 + 240 = 0x9d4d0 /\
  rom_chk SG RLO RHI (grant_obj 18 + 240 + 18) [16; 6; 2] = true /\
  rom_chk SG RLO RHI (grant_obj 18 + 240 + 2) (vbytes 2 1) = true /\
  rom_chk SG RLO RHI (grant_obj 18 + 240 + 8) (vbytes 0x211c0 8) = true /\
  rom_chk SG RLO RHI (grant_obj 18 + 240 + 16) (vbytes 18 1) = true /\
  rom_chk SG RLO RHI (grant_obj 18 + 240 + 17) (vbytes 3 1) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma b_tmpl_check : rom_chk SG RLO RHI 0x211c0 T32z = true.
Proof. vm_compute. reflexivity. Qed.
Lemma b_bgs_rows_check :
  grant_obj 22 = 0x21200 /\ grant_obj 23 = 0x21260 /\
  rom_chk SG RLO RHI (grant_obj 22) HEAD_ACK34z = true /\
  rom_chk SG RLO RHI (grant_obj 23) HEAD_MARK34z = true /\
  rom_chk SG RLO RHI (grant_obj 19) GBallz = true.
Proof. repeat split; vm_compute; reflexivity. Qed.
(* The same form for the regions the earlier lemmas check through romB8. *)
Lemma b_rom_checks :
  rom_chk SG RLO RHI (grant_obj 34) (vbytes 12297829382473034411 8) = true /\
  rom_chk SG RLO RHI (grant_obj 9) (T0z ++ repeat 0 34) = true /\
  rom_chk SG RLO RHI (grant_obj 4) HEAD_ACK34z = true /\
  rom_chk SG RLO RHI (grant_obj 5) HEAD_MARK34z = true /\
  rom_chk SG RLO RHI (grant_obj 6) POLLz = true /\
  rom_chk SG RLO RHI (grant_obj 15) (repeat 255 6) = true /\
  rom_chk SG RLO RHI (grant_obj 26 + 8) (vbytes (nth 2 lay_jt_slots 0 + grant_text - grant_obj 26) 4) = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Ltac img_in := cbn [GRANT_GLOBS_B In]; vm_compute (grant_obj _); repeat (first [left; reflexivity | right]).
Ltac img_bnd := unfold IMG_LO, IMG_HI; rewrite ?IMG_LO_B_val, ?IMG_TOP_B_val; vm_compute; discriminate.
(* ---- the corollaries ----------------------------------------------------------------------------------------
   Each takes `ro_free B a n` for the bytes it reads; the closing file discharges those at image B's own B. *)
Lemma img_next_div3 : ro_free B (grant_obj 34) 8 -> IMG_NEXT_DIV3 (PI := PI_grant) B.
Proof.
intros HF. unfold IMG_NEXT_DIV3. split; [img_bnd|]. split; [img_bnd|].
intros H mem HR. apply garr8_val_mem.
apply (arodata_garr8_rom SG RLO RHI B _ _ H mem); [exact (proj1 b_rom_checks) | | exact HR].
unfold vbytes. rewrite length_map, length_seq. exact HF.
Qed.

(* check_groupa's constant (object 9, 50 bytes). *)
Lemma img_check_groupa : ro_free B (grant_obj 9) 50 -> IMG_check_groupa (PI := PI_grant) B.
Proof.
intros HF. unfold IMG_check_groupa. split; [img_in|]. split; [img_bnd|]. split; [img_bnd|].
intros H mem HR. apply (arodata_garr8_rom SG RLO RHI B _ _ H mem); [exact (proj1 (proj2 b_rom_checks)) | | exact HR].
change (Z.of_nat (length (T0z ++ repeat 0 34))) with 50. exact HF.
Qed.

(* reac_ctrl_parse's .str.4 (object 15): its first six bytes are 0xff. *)
Lemma img_reac_ctrl_parse : ro_free B (grant_obj 15) 6 -> IMG_reac_ctrl_parse (PI := PI_grant) B.
Proof.
intros HF. unfold IMG_reac_ctrl_parse. split; [img_in|]. split; [img_bnd|]. split; [img_bnd|].
intros H mem HR i Hi.
assert (Hk : (Z.to_nat i < length (repeat 255 6))%nat) by (rewrite repeat_length; lia).
pose proof (arodata_aview_tbl_rom SG RLO RHI B (grant_obj 15) (repeat 255 6) H mem
  ltac:(exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 b_rom_checks)))))))
  ltac:(change (Z.of_nat (length (repeat 255 6))) with 6; exact HF) HR (Z.to_nat i) Hk) as Hv.
rewrite Z2Nat.id in Hv by lia.
assert (E : nth (Z.to_nat i) (repeat 255 6) 0 = 255).
{ rewrite repeat_length in Hk. set (k := Z.to_nat i) in *. clearbody k.
  do 6 (destruct k as [|k]; [reflexivity|]). lia. }
rewrite E in Hv. exact Hv.
Qed.

(* The entry function's four read-only tables (objects 4, 5, 6 and GRANT_GROUPB). *)
Lemma img_llvmf_sweep :
  ro_free B (grant_obj 4) 34 -> ro_free B (grant_obj 5) 34 -> ro_free B (grant_obj 6) 18 ->
  ro_free B (grant_obj 19) 204 -> IMG_LLVMF_SWEEP (PI := PI_grant) B.
Proof.
intros H4 H5 H6 H19. unfold IMG_LLVMF_SWEEP.
split; [|repeat (split; [solve [img_in | img_bnd]|]); solve [img_in | img_bnd]].
intros H mem HR. destruct b_rom_checks as (_ & _ & C4 & C5 & C6 & _ & _).
split; [|split; [|split]].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 4) HEAD_ACK34z H mem);
  [exact C4 | change (Z.of_nat (length HEAD_ACK34z)) with 34; exact H4 | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 5) HEAD_MARK34z H mem);
  [exact C5 | change (Z.of_nat (length HEAD_MARK34z)) with 34; exact H5 | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 6) POLLz H mem);
  [exact C6 | change (Z.of_nat (length POLLz)) with 18; exact H6 | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 19) GBallz H mem);
  [exact (proj2 (proj2 (proj2 (proj2 b_bgs_rows_check)))) |
   change (Z.of_nat (length GBallz)) with 204; exact H19 | exact HR].
Qed.

(* reac_ctrl_build_grant_sweep's three tables (objects 22, 23 and GRANT_GROUPB). *)
Lemma img_bgs_rows :
  ro_free B (grant_obj 22) 34 -> ro_free B (grant_obj 23) 34 -> ro_free B (grant_obj 19) 204 ->
  IMG_BGS_ROWS (PI := PI_grant) B.
Proof.
intros H22 H23 H19. unfold IMG_BGS_ROWS.
split; [|repeat (split; [solve [img_in | img_bnd]|]); solve [img_in | img_bnd]].
intros H mem HR. destruct b_bgs_rows_check as (_ & _ & C22 & C23 & C19).
split; [|split].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 22) HEAD_ACK34z H mem);
  [exact C22 | change (Z.of_nat (length HEAD_ACK34z)) with 34; exact H22 | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 23) HEAD_MARK34z H mem);
  [exact C23 | change (Z.of_nat (length HEAD_MARK34z)) with 34; exact H23 | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 19) GBallz H mem);
  [exact C19 | change (Z.of_nat (length GBallz)) with 204; exact H19 | exact HR].
Qed.

(* ctrl_finish's three row bytes, and ctrl_lay_block's four (the row is object 18 + 240). *)
Lemma img_ctrl_row_fin : ro_free B (grant_obj 18 + 240) 24 -> IMG_CTRL_ROW_FIN (PI := PI_grant) B.
Proof.
intros HF. unfold IMG_CTRL_ROW_FIN, B_ROW. intros H mem HR.
apply (arodata_garr8_rom SG RLO RHI B (grant_obj 18 + 240 + 18) [16; 6; 2] H mem);
 [exact (proj1 (proj2 b_row_check)) | change (Z.of_nat (length [16; 6; 2])) with 3; intros a Ha; apply HF; lia | exact HR].
Qed.
Lemma img_ctrl_row_lay : ro_free B (grant_obj 18 + 240) 24 -> IMG_CTRL_ROW_LAY (PI := PI_grant) B 0x211c0.
Proof.
intros HF. unfold IMG_CTRL_ROW_LAY, B_ROW. intros H mem HR.
destruct b_row_check as (_ & _ & Ck & Ctm & Cao & Cal).
split; [|split; [|split]]; apply garr8_val_mem.
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 18 + 240 + 2) (vbytes 2 1) H mem);
  [exact Ck | unfold vbytes; rewrite length_map, length_seq; intros a Ha; apply HF; lia | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 18 + 240 + 8) (vbytes 0x211c0 8) H mem);
  [exact Ctm | unfold vbytes; rewrite length_map, length_seq; intros a Ha; apply HF; lia | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 18 + 240 + 16) (vbytes 18 1) H mem);
  [exact Cao | unfold vbytes; rewrite length_map, length_seq; intros a Ha; apply HF; lia | exact HR].
- apply (arodata_garr8_rom SG RLO RHI B (grant_obj 18 + 240 + 17) (vbytes 3 1) H mem);
  [exact Cal | unfold vbytes; rewrite length_map, length_seq; intros a Ha; apply HF; lia | exact HR].
Qed.
(* The template's 32 bytes (TM = 0x211c0), the garr8 conjunct of IMG_CTRL_TMPL. *)
Lemma img_ctrl_tmpl_bytes : ro_free B 0x211c0 32 ->
  forall (H : word -> bool) mem, arodata_okP SG RLO RHI B (aview SG H mem) ->
  garr8 SG (mrestrict H mem) 0x211c0 T32z.
Proof.
intros HF H mem HR.
apply (arodata_garr8_rom SG RLO RHI B 0x211c0 T32z H mem);
 [exact b_tmpl_check | change (Z.of_nat (length T32z)) with 32; exact HF | exact HR].
Qed.
End a.
