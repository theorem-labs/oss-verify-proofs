(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 2069 of its 2189 lines of code are new or changed and 584 lines of the source are left out. *)
(* fuzz_preset lib/B, parse_string on image B (asan-ubsan build): the \u STRETCH of the walk, psb_u_holdsP / psb_u_holds.
   rule 24: proves no function (kind: segment lemma). psb_u_holdsP proves PSB_Base.v's psb_seg_uP (the \u escape at
   PSB_U) at an ABSTRACT memory invariant P with srr_inv_laws segs P and srr_inv_call segs P (the stretch crosses the kit-text
   calls hex4 and put_utf8), from psb_seg_freeP P and the measure-indexed decode head psb_dec_ltP P m; it ends in
   ps_postPR P (wle' segs RZ_cf) D (SRr' segs RZ_cf: it may reach the bad escape's fuzz_free); its pieces run at wle
   into PS_Gen's hand-off form ps_finP. P is carried as ps_carryP's last conjunct at every cut; across a call it follows
   from the callee's m-form post (fpostWm / fpostm: memnorm memc -> memnorm mem') by srr_inv_call; across the store of
   the pair (the frame word sp + 36) it is the invariant runner twins' end keep (paj_run_x_m_inv / paj_run_to_x_m_inv at
   PLAW);
   the read-only runs leave the memory as it was. The old psb_u_holds is kept, statement unchanged (it did not move: the
   callee keep is the texts', no premise was added), as the corollary at P := fun _ => True.
   Base: the kit's cut 7cdbb61b5fa0 (PRH_FnReader.v f1ae32e3b2cd, PRH_Base.v ef7c8ca98529; this row's PS_Gen.v, PSB_Base.v,
   PSB_Src.v; YCbqG.v 219748197d6b, YCbqGcallW.v fb6aa11676a2, YC80x.v 14f84f225e8f, YC1fPx.v 7814b594066f,
   YSRrMemnorm.v 5ffa8525936b; PRW_StepKit.v 0df3991c13f4; B Listing_prog.v c97cc46b3e13 / PAImg_prog.v 15fab93fe702);
   earlier a working branch 6225fcbb328 (the generic-P base + the OLD-PIN KIT OF RECORD a working branch
   preset-tree-at-2026-10-29T13-54-32Z.tsv (sha256 14e543909afe; internal record): PRH_FnReader.v 66e11f202508, PRH_Base.v ee6c7a38d6b6; engine s1b preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record)). Ported from
   a working branch 8bd080be638 (base 8860ed3a414), where psb_u_holds was Qed first.
   Neutral listing (parse_string, B entry 0x87c0c): parse_string.fuzz_preset.asan-ubsan.s (sha256 549ddc2d23bf; internal record).
   THE CODE WALKED (offsets from parse_string's entry, DERIVED from the listing; names in PSB_Base / here):
     436 (PSB_U)  a0 = end - (r + 2) < 4 -> PSB_FREE (psu_dec_short_at); `jal hex4` at 456 (a0 = r + 2, a1 = sp + 36)
     460          hex4 = -1 -> FREE; h = lw sp+36; h = 0 -> FREE; UBSan bltu -5 s5 (not taken, the cursor's range);
                  h & -1024 = 55296 -> 868; = 56320 -> FREE; else s5 = r + 6, j 1032
     868          q + 8 shadow (0), end - (r + 6) < 6 -> FREE; text[r + 6] shadow (src_rd) and byte = 92 (else FREE),
                  text[r + 7] shadow and byte = 117 (else FREE); UBSan checks (not taken); `jal hex4` at 968
                  (a0 = r + 8, a1 = sp + 32)
     972          hex4 = -1 -> FREE; lo = lw sp+32; lo - 57344 <u -1024 test (else FREE); cp = pair_cp h lo stored at
                  sp + 36 (the frame window psb_inv_store keeps the invariant across), s5 = r + 12
     1032         `jal put_utf8` at 1040 (a0 = w, a1 = cp; footprint [w, w + len) inside out)
     1044         a4 .. t0 reloaded; UBSan wrap check on w + len (not taken); w += len; j 544: q + 8 shadow, a0 = end,
                  s4 = s5, bltu s5, end -> PSB_DEC (psb_dec_lt at a smaller measure)
   Calls: hex4 through YCbqGcallW.aj_call_xW_sp at e1 = 48 (thex4_specX's fpostWm window holds sp + 32 / sp + 36),
   put_utf8 through aj_call_xW_sp at e1 = 0 with fpostW_x_of_apost (tput_utf8_specX is fpostm); fpre's
   `spZ + 64 <= ly_stk_hi` from the entry's stack bound and `raZ < YM05.alloc_ceiling` from the jal's return pc
   BASE + (PSB_OFF + 460 / 972 / 1044) (closed: BASE < 2 ^ 40 by vm_compute); the callee chain from s0 = q by ps_chain_call_offq and
   psb_s0_q; after each call psb_after_call (cj_kept_trans, alx_hshadow for out's shadow, PSB_Src's
   psb_src_after_call for the text).
   NUMERALS (classified): ADDRESS none typed (BASE, PSB_OFF, SIGMA by name; the return sites as BASE + (PSB_OFF +
   460 / 972 / 1044)); DERIVED: the listing offsets 436 .. 1044 above, the frame slots -144 .. -104 (sp + 0 .. 40
   off the entry sp), q's fields 8 / 16, the engine's atom numbers (0 .. 66, 512 ..); LENGTH: 144 (frame), 4 / 6 /
   12 (escape lengths), 8 (word), 4096 (page), 2 ^ 40 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (range bounds); WORD: the
   characters 34 / 92 / 117, the code-point constants 0, 1024, 55296, 56319, 56320, 57343, 57344, 65535, 65536,
   1114111, -56613888 (pair_cp's additive constant) and its 2 ^ 64 residue 18446744073652937728, -1024 and its residue
   18446744073709550592, -57344, 32 / 101 / 91 / 113 / 114 (decode constants), 256 (byte range).
   SECTION HYPOTHESES: LAWS, TL, PST_ok, HHEX4, HPUTU (the internal file STRETCH-BRIEF.md's texts), ZSA, IMGV (PSB_Src.v's, verbatim);
   inside Section pu only: P, PLAW (srr_inv_laws segs P), PCALL (srr_inv_call segs P), which psb_u_holdsP quantifies. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PS_Gen PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PSB_Base PSB_Src.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- pure layer: the text after a backslash-u, decode's and scan's one step (PjGrammar) ---- *)
Lemma psu_skipn_cons : forall {A : Type} (l : list A) n b, nth_error l n = Some b -> skipn n l = b :: skipn (S n) l.
Proof. intros A l. induction l as [|x l IH]; intros [|n] b H; cbn in *; try discriminate; [injection H as ->; reflexivity | apply IH; exact H]. Qed.
Lemma psu_rest_cons : forall tb text r b, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some b ->
  rest_atR tb text r = b :: rest_atR tb text (r + 1).
Proof. intros tb text r b Hr H. unfold rest_atR. rewrite (psu_skipn_cons _ _ _ H). f_equal. f_equal. lia. Qed.
Lemma psu_rest_len : forall tb text r, text <= r ->
  Z.of_nat (length (rest_atR tb text r)) = Z.max 0 (Z.of_nat (length tb) - (r - text)).
Proof. intros tb text r Hr. unfold rest_atR. rewrite length_skipn. lia. Qed.
Lemma psu_rest_nth : forall tb text r i, text <= r -> 0 <= i ->
  nth_error (rest_atR tb text r) (Z.to_nat i) = nth_error tb (Z.to_nat (r + i - text)).
Proof. intros tb text r i Hr Hi. unfold rest_atR. rewrite nth_error_skipn. f_equal. lia. Qed.
Lemma psu_hexval_ne : forall d v, PjGrammar.hexval d = Some v -> d <> 34 /\ d <> 92 /\ 0 <= v < 16.
Proof.
intros d v H. unfold PjGrammar.hexval in H.
destruct ((48 <=? d) && (d <=? 57)) eqn:E1;
  [apply andb_prop in E1 as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; injection H as <-; lia|].
destruct ((97 <=? d) && (d <=? 102)) eqn:E3;
  [apply andb_prop in E3 as [E3 E4]; apply Z.leb_le in E3; apply Z.leb_le in E4; injection H as <-; lia|].
destruct ((65 <=? d) && (d <=? 70)) eqn:E5;
  [apply andb_prop in E5 as [E5 E6]; apply Z.leb_le in E5; apply Z.leb_le in E6; injection H as <-; lia|].
discriminate.
Qed.
Lemma psu_hex4_some : forall d0 d1 d2 d3 x h, PjGrammar.hex4 (d0 :: d1 :: d2 :: d3 :: x) = Some h ->
  0 <= h < 65536 /\ d0 <> 34 /\ d0 <> 92 /\ d1 <> 34 /\ d1 <> 92 /\ d2 <> 34 /\ d2 <> 92 /\ d3 <> 34 /\ d3 <> 92.
Proof.
intros d0 d1 d2 d3 x h H. cbn [PjGrammar.hex4] in H.
destruct (PjGrammar.hexval d0) as [v0|] eqn:E0; [|discriminate].
destruct (PjGrammar.hexval d1) as [v1|] eqn:E1; [|discriminate].
destruct (PjGrammar.hexval d2) as [v2|] eqn:E2; [|discriminate].
destruct (PjGrammar.hexval d3) as [v3|] eqn:E3; [|discriminate].
injection H as <-. apply psu_hexval_ne in E0, E1, E2, E3. lia.
Qed.
Lemma psu_hex4_firstn : forall x, PjGrammar.hex4 (firstn 4 x) = PjGrammar.hex4 x.
Proof. intros [|d0 [|d1 [|d2 [|d3 x]]]]; reflexivity. Qed.
Lemma psu_dec_u4 : forall d0 d1 d2 d3 r3, PjGrammar.decode (92 :: 117 :: d0 :: d1 :: d2 :: d3 :: r3) =
  match PjGrammar.hex4 [d0; d1; d2; d3] with
  | None => None
  | Some cp =>
    if cp =? 0 then None
    else if (55296 <=? cp) && (cp <? 56320) then
      match r3 with
      | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
        match PjGrammar.low r3 with
        | Some lo => PjGrammar.emit (PjGrammar.utf8 (PjGrammar.pair_cp cp lo)) (PjGrammar.decode r4)
        | None => None
        end
      | _ => None
      end
    else if (56320 <=? cp) && (cp <? 57344) then None
    else PjGrammar.emit (PjGrammar.utf8 cp) (PjGrammar.decode r3)
  end.
Proof. reflexivity. Qed.
Lemma psu_dec_short : forall r2, (length r2 < 4)%nat -> PjGrammar.decode (92 :: 117 :: r2) = None.
Proof. intros r2 H. destruct r2 as [|d0 [|d1 [|d2 [|d3 r3]]]]; cbn [length] in H; try lia; reflexivity. Qed.
Lemma psu_scan_u4 : forall d0 d1 d2 d3 r3 h, PjGrammar.hex4 (d0 :: d1 :: d2 :: d3 :: r3) = Some h ->
  PjGrammar.scan (92 :: 117 :: d0 :: d1 :: d2 :: d3 :: r3) = option_map (fun q => (6 + q)%nat) (PjGrammar.scan r3).
Proof.
intros d0 d1 d2 d3 r3 h H. apply psu_hex4_some in H as (_ & A0 & B0 & A1 & B1 & A2 & B2 & A3 & B3).
cbn [PjGrammar.scan]. replace (92 =? 34) with false by reflexivity. replace (92 =? 92) with true by reflexivity.
rewrite (proj2 (Z.eqb_neq d0 34) A0), (proj2 (Z.eqb_neq d0 92) B0), (proj2 (Z.eqb_neq d1 34) A1).
rewrite (proj2 (Z.eqb_neq d1 92) B1), (proj2 (Z.eqb_neq d2 34) A2), (proj2 (Z.eqb_neq d2 92) B2).
rewrite (proj2 (Z.eqb_neq d3 34) A3), (proj2 (Z.eqb_neq d3 92) B3).
destruct (PjGrammar.scan r3); reflexivity.
Qed.
(* a value chunk of 8 bytes reads the same word as its value mod 2 ^ 64 *)
Lemma psu_val_mem_mod : forall segs m a v, val_mem segs m a 8 v -> val_mem segs m a 8 (v mod 2 ^ 64).
Proof. intros segs m a v H k Hk. rewrite H by exact Hk. unfold YO0f.le_byte. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* ---- the symbolic states (atoms only: 0..31 the entry registers, 32..63 the current registers at the stretch's
   start, 64.. the stretch's extra values) ---- *)
(* the register file: every register its current atom but x0, sp (the entry sp atom 2 less the frame), gp / tp (the
   entry's atoms: ps_gptp), s1 (q + 8 off s0's atom), a0 and s5 (given), the shadow base s7 and the constants s9 / s10 / s11 *)
Definition psb_sr (a0 s5 : sv) : list sv :=
  [SLit 0; SOff 33 0; SOff 2 (-144); SOff 3 0; SOff 4 0; SOff 37 0; SOff 38 0; SOff 39 0; SOff 40 0; SOff 40 8;
   a0; SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0;
   SOff 52 0; s5; SOff 54 0; SLit SHADOW_OFF; SOff 56 0; SLit 34; SLit (-1); SLit 92; SOff 60 0; SOff 61 0;
   SOff 62 0; SOff 63 0].
(* the three surrogate words of the frame (sp + 24, sp + 16, sp + 8: offsets -120, -128, -136 off the entry sp) *)
Definition psb_sur : list YP09.chunk :=
  [YP09.mkChunk (-120) (CVal 8 (SLit 55296)); YP09.mkChunk (-128) (CVal 8 (SLit 56320));
   YP09.mkChunk (-136) (CVal 8 (SLit 18446744073652937728))].
(* parse_string's frame below the entry sp, write window [wlo, whi), chunks cs and the surrogate words *)
Definition psb_rg_frame (wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-144) 0 wlo whi (cs ++ psb_sur).
(* in->end, the q + 8 word (off s0's atom 40), its value atom 64 *)
Definition psb_rg_qe : YP09.region := YP09.mkRegion (Some 40%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 64 0))].
(* the shadow cell of q + 8 (s8's atom 56): 0 *)
Definition psb_rg_sh8 : YP09.region := YP09.mkRegion (Some 56%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* text[r + 6], text[r + 7] (off s4's atom 52), their value atoms 66 / 67 *)
Definition psb_rg_t67 : YP09.region :=
  YP09.mkRegion (Some 52%nat) 6 8 0 0 [YP09.mkChunk 6 (CVal 1 (SOff 66 0)); YP09.mkChunk 7 (CVal 1 (SOff 67 0))].
Definition PSB_Bx : sv := SLit SHADOW_OFF.
Definition PSB_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the stack atom's range, and a pointer's (below the stack band) *)
Definition psb_af_sp : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition psb_af_ptr : afact := mkAF 4096 (2 ^ 47 - 2 ^ 23) 0.

Section psu. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PSB_PrhImg PSB_PAListing PSB_PAImg.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
#[local] Notation VAL := (@pa_val _ B_prog_listing PSB_PAImg).
#[local] Notation BASE := (@pa_val _ B_prog_listing PSB_PAImg A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PSB_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation PST := (prh_pst (PI := PSB_PrhImg)).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
#[local] Notation KEPT := (cj_kept (SK := SK) segs B PST).
#[local] Notation LEDGER := (prh_ledger (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_in := (ps_in (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_SP := (PS_SP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_carry := (ps_carry (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_alloc := (ps_alloc (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_pre := (ps_pre (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx).
#[local] Notation ps_post := (ps_post (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_gptp := (ps_gptp (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_dec_rel := (ps_dec_rel (L := B_prog_listing) (PA := PSB_PAImg)).

(* ---- the Section hypotheses (the internal file STRETCH-BRIEF.md; ZSA / IMGV are PSB_Src.v's, BParseString's agreement) ---- *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis TL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis HHEX4 : thex4_specX (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK.
Hypothesis HPUTU : tput_utf8_specX (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK.
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : psb_img_shadow_vis ARx.

(* ---- THE GENERIC INVARIANT (the internal file GP-BRIEF.md; a Theorem Labs lane 12:18Z / 12:22Z): every proof below is over an ABSTRACT P with
   its run laws PLAW and its call law PCALL (the stretch crosses the kit-text calls hex4 and put_utf8, whose m-form posts give
   the memnorm keep); the top (BParseString's) instantiates P once per record as PS_Gen's ps_mn D. ---- *)
Section pu.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.
#[local] Notation ps_carry := (ps_carryP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).
(* THE HAND-OFF FORM (PS_Gen): the pieces run at wle into ps_finP, the SRr' fact of the stretch they hand to (the back
   edge to PSB_DEC and the free cut, both of which may cross the bad escape's fuzz_free: ps_finP_hand); the stretch is
   made SRr' once, at its entry (ps_finP_SRr' in psb_u_holdsP) *)
#[local] Notation ps_post := (ps_finP (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).

(* ---- the environment of a stretch ---- *)
Definition psb_cur (regs : bvmap 5 word) : list word := map (getr regs) all_regs.
Definition psb_E (D : ps_in) (regs : bvmap 5 word) (X : list word) : env :=
  Eimg (L := B_prog_listing) (PI := PSB_PAImg) (Ereg (pi_regs D) (psb_cur regs ++ X)).
Lemma psb_ew_hi : forall D regs X n, (32 <= n < A_TEXT)%nat ->
  ew (psb_E D regs X) n = nth (n - 32) (psb_cur regs ++ X) (Z_to_bv 64 0).
Proof.
intros D regs X n Hn. unfold psb_E. rewrite Eimg_low by lia. unfold Ereg. cbn [ew].
replace (n <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.
Lemma psb_ew_lo : forall D regs X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (psb_E D regs X) n = getr (pi_regs D) r.
Proof.
intros D regs X n r H. pose proof (u5_range r). unfold psb_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat (pi_regs D) _ n r H).
Qed.
Lemma psb_frame : PS_FRAME (PI := PSB_PrhImg) = 144.
Proof. vm_compute. reflexivity. Qed.
Lemma psb_env_img : forall D regs X, img_env VAL A_LIM (psb_E D regs X).
Proof. intros D regs X. apply Eimg_env. Qed.

(* one register of a fresh stretch state: its sv against the concrete file *)
Ltac psb_reg_tac :=
  match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  first
  [ rewrite getr_zero; reflexivity
  | lazymatch goal with |- _ = sv_denot _ (SOff ?n 0) => lazymatch eval cbv in (Nat.leb 32 n) with true =>
      cbn [sv_denot]; rewrite psb_ew_hi by (unfold A_TEXT; lia);
      cbn [Nat.sub nth psb_cur map all_regs app]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end end
  | lazymatch goal with |- _ = sv_denot _ (SOff ?n ?z) => lazymatch eval cbv in (Nat.leb 32 n) with true =>
      cbn [sv_denot]; rewrite psb_ew_hi by (unfold A_TEXT; lia);
      cbn [Nat.sub nth psb_cur map all_regs app] end end;
    match goal with
    | H : getr ?rg ?rr = w64 _, H2 : getr ?rg ?rr2 = w64 _ |- getr ?rg ?rr = Z_to_bv 64 (bv_unsigned (getr ?rg ?rr2) + _) =>
        rewrite H, H2; unfold w64; rewrite unsigned_lit_small; [f_equal; lia | lia] end
  | match goal with H : getr ?rg ?rr = w64 _ |- getr ?rg ?rr = sv_denot _ (SLit _) => rewrite H; reflexivity end
  | match goal with H : getr ?rg 2 = w64 _ |- getr ?rg 2 = sv_denot _ (SOff 2 _) =>
      cbn [sv_denot]; rewrite (psb_ew_lo _ _ _ 2 2 eq_refl), H; unfold w64, PS_Gen.PS_SP, spZ;
      rewrite psb_frame; f_equal; lia end
  | match goal with H : getr ?rg 3 = getr _ 3 |- getr ?rg 3 = sv_denot _ (SOff 3 0) =>
      cbn [sv_denot]; rewrite (psb_ew_lo _ _ _ 3 3 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H end
  | match goal with H : getr ?rg 4 = getr _ 4 |- getr ?rg 4 = sv_denot _ (SOff 4 0) =>
      cbn [sv_denot]; rewrite (psb_ew_lo _ _ _ 4 4 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H end ].
Ltac psb_regs_ok := apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<-|Hrr]; [psb_reg_tac|]); destruct Hrr.

Lemma psu_scan_lt_k : forall k x n, (length x <= k)%nat -> PjGrammar.scan x = Some n -> (n < length x)%nat.
Proof.
induction k as [|k IH]; intros x n Hk H; destruct x as [|b r]; cbn [PjGrammar.scan length] in *; try discriminate; try lia.
destruct (b =? 34); [injection H as <-; lia|].
destruct (b =? 92).
- destruct r as [|e r2]; [discriminate|]. destruct (PjGrammar.scan r2) as [q|] eqn:E; [|discriminate].
  cbn [option_map length] in *. injection H as <-. pose proof (IH r2 q ltac:(lia) E). lia.
- destruct (PjGrammar.scan r) as [q|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
  pose proof (IH r q ltac:(lia) E). lia.
Qed.
Lemma psu_scan_lt : forall x n, PjGrammar.scan x = Some n -> (n < length x)%nat.
Proof. intros x n H. exact (psu_scan_lt_k (length x) x n (le_n _) H). Qed.

(* ---- the stretch invariant: what every stretch start of the \u stretch knows (psb_at_u without a0, s5 and the
   clobbered decode constants a4 .. t0) ---- *)
Definition psb_inv (D : ps_in) ly S Hp (W : world segs) (regs : bvmap 5 word) mem md (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carry D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ psb_sh_regs D regs /\
  ps_gptp D regs /\ getr regs 25 = w64 34 /\ getr regs 26 = w64 (-1) /\ getr regs 27 = w64 92 /\
  val_mem segs (rdW W mem) (PS_SP D + 24) 8%nat 55296 /\
  val_mem segs (rdW W mem) (PS_SP D + 16) 8%nat 56320 /\
  val_mem segs (rdW W mem) (PS_SP D + 8) 8%nat (-56613888) /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs (@pa_relro_lo _ B_prog_listing PSB_PAImg) (@pa_relro_hi _ B_prog_listing PSB_PAImg) B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  nth_error (pi_tb D) (Z.to_nat (r - pi_text D)) = Some 92 /\
  nth_error (pi_tb D) (Z.to_nat (r + 1 - pi_text D)) = Some 117 /\
  ps_dec_rel D W mem out w r Q.

(* the ranges every stretch's facts state: the entry sp, the text and the cursor (below the stack band) *)
Lemma psb_ranges : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  2 ^ 46 <= spZ (pi_regs D) <= 2 ^ 47 /\ spZ (pi_regs D) mod 16 = 0 /\
  4096 <= pi_text D /\ pi_text D + pi_len D <= YM05.alloc_ceiling /\ YM05.alloc_ceiling <= 2 ^ 47 - 2 ^ 23 /\
  pi_text D <= pi_p D /\ pi_p D + 1 <= r /\ r + 2 <= pi_p D + 1 + Z.of_nat Q < pi_text D + pi_len D /\
  Z.of_nat (length (pi_tb D)) = pi_len D.
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HI.
pose proof HPRE as (((_ & _ & _ & _ & _ & Hstk & _) & _) & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
destruct HI as ((k & _ & _ & _ & HSRC & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _ & HSC & _ & _ & _ & _ & _ & _ &
  Hb0 & Hb1 & HDR).
destruct HSRC as (_ & H4096 & Hcl & _).
destruct HPJ as (_ & _ & _ & _ & _ & Ht0 & Htl & Hpr & Hlen & _).
destruct HDR as (done & _ & _ & _ & _ & Hr & _ & _ & Hsr).
assert (Hx : (Q < length (ps_x D))%nat) by exact (psu_scan_lt _ _ HSC).
unfold ps_x, rest_atR in Hx. rewrite length_skipn in Hx.
(* r and r + 1 are text bytes, and r + 1 is not the closing quote *)
assert (Hquote : r + 1 < pi_p D + 1 + Z.of_nat Q).
{ assert (Hs2 := Hsr). rewrite (psu_rest_cons _ _ r 92) in Hs2 by (lia || exact Hb0).
  rewrite (psu_rest_cons _ _ (r + 1) 117) in Hs2 by (lia || exact Hb1).
  cbn [PjGrammar.scan] in Hs2. replace (92 =? 34) with false in Hs2 by reflexivity.
  replace (92 =? 92) with true in Hs2 by reflexivity.
  destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 1 + 1))) as [q2|]; [|discriminate].
  cbn in Hs2. injection Hs2 as Hs2. lia. }
clear - Hal Hstk0 Hceil Hslo Hshi H47 C1 H4096 Hcl Ht0 Htl Hpr Hlen Hr Hx Hquote. unfold spZ in *. lia.
Qed.

(* an atom of a stretch environment, by its number *)
Ltac psb_ew :=
  repeat match goal with
  | |- context [ew (psb_E ?D ?regs ?X) ?n] =>
    lazymatch eval cbv in (Nat.ltb n 32) with
    | true => first [ rewrite (psb_ew_lo D regs X n 1 eq_refl) | rewrite (psb_ew_lo D regs X n 2 eq_refl)
                    | rewrite (psb_ew_lo D regs X n 3 eq_refl) | rewrite (psb_ew_lo D regs X n 4 eq_refl) ]
    | false => rewrite (psb_ew_hi D regs X n) by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs app]
    end
  end.
(* an afact of a stretch's facts: the atom's value and its bounds *)
Ltac psb_fact_tac :=
  unfold afact_ok; cbn [af_lo af_hi af_al2 psb_af_sp psb_af_ptr]; psb_ew;
  repeat match goal with H : getr ?rg ?rr = w64 _ |- context [bv_unsigned (getr ?rg ?rr)] => rewrite H end;
  unfold w64, spZ in *; rewrite ?unsigned_lit_small by lia; change (2 ^ 4) with 16; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
  repeat split; lia.

Definition psb_factsA : facts := mkFacts [(2%nat, psb_af_sp); (52%nat, psb_af_ptr); (42%nat, psb_af_ptr)] [] [].

(* the stretch at PSB_U: no region (436 .. 456 reads no memory) *)
Lemma psb_stA : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 10 = w64 (pi_text D + pi_len D) -> getr regs 21 = w64 (r + 2) ->
  st_ok_pi segs VAL (psb_E D regs []) (mkSS (PSB_OFF + PSB_U) (psb_sr (SOff 42 0) (SOff 52 2)) [] None psb_factsA)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + PSB_U))) mem (seg_rom segs))).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HI H10 H21.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
destruct HI as (_ & _ & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & _ & _ & _ & _ & _ & _ & Hsp & H18 & H19 & H20 &
  H8 & H9 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
pose proof HWIN as (He0 & _ & Hetop & _).
pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- psb_regs_ok.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; exact I]. cbn [psb_factsA f_atoms atoms_ok].
  split; [psb_fact_tac|]. split; [psb_fact_tac|]. split; [psb_fact_tac|exact I].
Qed.

(* a stack byte's shadow cell reads 0 (the stack-shadow law), as the one-byte value 0 *)
Lemma psb_val_mem_sh0 : forall ly S Hp (W : world segs) mem md a,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
  val_mem segs (rdW W mem) (SHADOW_OFF + a / 8) 1 0.
Proof.
intros ly S Hp W mem md a HAR Ha j Hj. assert (j = 0%nat) by lia. subst j.
pose proof (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md a HAR Ha) as Hz.
destruct (aview_byte segs (w_H W) mem (SHADOW_OFF + a / 8) 0 Hz) as (b & Hb & Hv & _).
rewrite Z.add_0_r. rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Hv. reflexivity.
Qed.

Definition psb_hslot (o : Z) (n : nat) : YP09.chunk := YP09.mkChunk o (CVal 4 (SOff n 0)).
Definition psb_factsB : facts :=
  mkFacts [(2%nat, psb_af_sp); (52%nat, psb_af_ptr); (42%nat, mkAF 0 0 0); (65%nat, mkAF 0 65535 0);
           (64%nat, psb_af_ptr)] [] [].
(* the extra atoms after the first hex4: in->end, the digit value h, text[r + 6], text[r + 7] *)
Definition psb_XB (D : ps_in) (r h : Z) : list word :=
  [w64 (pi_text D + pi_len D); w64 h;
   w64 (nth (Z.to_nat (r + 6 - pi_text D)) (pi_tb D) 0); w64 (nth (Z.to_nat (r + 7 - pi_text D)) (pi_tb D) 0)].

(* a value chunk of a region from the val_mem fact Hs that holds its bytes *)
Ltac psb_chunk Hs :=
  lazymatch goal with |- YP09.chunk_ok _ ?E0 ?m ?b {| c_off := ?o; YP09.c_val := CVal ?n ?e |} =>
  lazymatch type of Hs with val_mem _ _ ?a _ ?v =>
    apply (chunk_ok_val _ E0 m b o n e v);
    [ cbn [sv_denot]; psb_ew; unfold w64; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia
    | cbn; lia
    | replace (b + o) with a by (unfold PS_Gen.PS_SP, spZ in *; rewrite ?psb_frame in *; lia); exact Hs ]
  end end.
(* a region's bounds, base and window, after its base atom is read off *)
Ltac psb_region_head :=
  unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val psb_rg_frame psb_rg_qe
       psb_rg_sh8 psb_rg_t67 app]; unfold psb_hslot, psb_sur; cbn [app]; psb_ew;
  repeat match goal with H : getr ?rg ?rr = w64 _ |- context [bv_unsigned (getr ?rg ?rr)] => rewrite H end;
  unfold w64, spZ in *.

Lemma psb_stB : forall CTX CW D ly S Hp W regs mem md out w r Q h,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 10 = w64 0 -> getr regs 21 = w64 (r + 2) ->
  val_mem segs (rdW W mem) (PS_SP D + 36) 4 h -> 0 <= h < 65536 ->
  st_ok_pi segs VAL (psb_E D regs (psb_XB D r h))
    (mkSS (PSB_OFF + 460) (psb_sr (SLit 0) (SOff 52 2)) [psb_rg_frame 0 0 [psb_hslot (-108) 65]; psb_rg_qe; psb_rg_sh8] None
       psb_factsB)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + 460))) mem (seg_rom segs))).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q h HPRE HI H10 H21 Hh Hh0. unfold psb_XB.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
destruct HI as ((k & HJ & _) & _ & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & _ & _ &
  Hsp & H18 & H19 & H20 & H8 & H9 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
pose proof HWIN as (He0 & _ & Hetop & _).
pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Ely_top & Ely_lo & Ely_hi & _).
pose proof (psu_val_mem_mod _ _ _ _ V8) as V8'. change ((-56613888) mod 2 ^ 64) with 18446744073652937728 in V8'.
pose proof HPJ as (_ & Vend & _).
assert (Vsh : val_mem segs (rdW W mem) (SHADOW_OFF + (pi_q D + 8) / 8) 1 0).
{ apply (psb_val_mem_sh0 ly S Hp W mem md); [exact HAR|]. rewrite Ely_lo, Ely_hi. unfold spZ in *. lia. }
pose proof asan_consts as (C1 & _).
assert (Hdq : 0 <= (pi_q D + 8) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold spZ in *; lia).
assert (Rcell : 0 <= SHADOW_OFF + (pi_q D + 8) / 8 < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (Rq : 0 <= pi_q D < 2 ^ 64) by (unfold spZ in *; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- psb_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; psb_region_head; rewrite ?(unsigned_lit_small _ Rcell), ?(unsigned_lit_small _ Rq).
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil; [psb_chunk Hh | psb_chunk V24 | psb_chunk V16 | psb_chunk V8'].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil. psb_chunk Vend.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil. psb_chunk Vsh.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. psb_region_head. rewrite ?(unsigned_lit_small _ Rcell), ?(unsigned_lit_small _ Rq).
  unfold SHADOW_OFF in *. repeat split; try exact I; lia.
- split; [|split; exact I]. cbn [psb_factsB f_atoms atoms_ok].
  repeat (split; [psb_fact_tac|]). exact I.
Qed.


(* ---- the facts a call leaves: the generic part of the hex4 and put_utf8 calls ---- *)
Lemma psb_val_mem_keep : forall (W W2 : world segs) mem mem2 a n v,
  (forall i, 0 <= i < Z.of_nat n -> aview segs (w_H W2) mem2 (a + i) = aview segs (w_H W) mem (a + i)) ->
  val_mem segs (rdW W mem) a n v -> val_mem segs (rdW W2 mem2) a n v.
Proof.
intros W W2 mem mem2 a n v H Hv j Hj.
rewrite (mbyte_of_aview segs (w_H W) (w_H W2) mem mem2 (a + Z.of_nat j)) by (apply H; lia). exact (Hv j Hj).
Qed.
Lemma psb_garr8_keep : forall (W W2 : world segs) mem mem2 a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs (w_H W2) mem2 (a + i) = aview segs (w_H W) mem (a + i)) ->
  garr8 segs (rdW W mem) a l -> garr8 segs (rdW W2 mem2) a l.
Proof.
intros W W2 mem mem2 a l H. apply psb_src_garr8. intros j Hj. apply H. lia.
Qed.
(* the kept relation does not look at the model's materialised pages *)
Lemma psb_kept_md : forall STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 md3,
  KEPT STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 -> same_but_materialized md2 md3 ->
  KEPT STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 W2 mem2 md3.
Proof.
intros STKf sp OR FPc lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hs.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hs)).
Qed.
(* a stretch's own run, with no write, only materialises pages: the carried facts move to the run's model *)
Lemma psb_carry_md : forall (D : ps_in) ly S Hp W mem md md' k,
  ps_carry D ly S Hp W mem md k [] ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly S Hp W mem md' k ->
  same_but_materialized md md' -> ps_carry D ly S Hp W mem md' k [].
Proof.
intros D ly S Hp W mem md md' k (_ & HK & HR) HJ Hs. split; [exact HJ|]. split; [|exact HR].
exact (psb_kept_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK Hs).
Qed.

(* the stack-window and block facts of the call state: the text is no byte of out's block *)
Lemma psb_text_out : forall (D : ps_in) ly S Hp W mem md out Q a,
  ARx ly S Hp W mem md -> ps_alloc D ly S Hp W mem out Q ->
  prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) ->
  pi_text D <= a < pi_text D + pi_len D -> ~ (out - cf_head <= a < out + Z.of_nat Q + 1).
Proof.
intros D ly S Hp W mem md out Q a HAR HAL HHOME Ha Hx.
destruct HAL as (_ & H4112 & _ & EHp & Eab & HL & _).
pose proof cf_head_nonneg as Hh0.
assert (Hin : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Rq : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
assert (Hnimg : ~ in_img segs a)
  by (refine (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HAR Hin _); rewrite Rq; lia).
pose proof HL as (_ & HND & HFA & HPERM).
destruct HHOME as [[(b & m & HinL & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & HinA & Hnh & Hb & Hm)].
- (* a harness block of the entry ledger: another block than out's *)
  assert (HinL' : In (b, m) ((out, Z.of_nat Q + 1) :: pi_Lam D)) by (right; exact HinL).
  pose proof (proj1 (Forall_forall _ _) HFA _ HinL') as (Hm0 & Hbl & _ & _ & _). cbn [fst snd] in Hm0, Hbl.
  assert (Hne : b <> out).
  { intros ->. cbn [map fst] in HND. apply NoDup_ListNoDup in HND. apply NoDup_cons_iff in HND as [HN _]. apply HN.
    change out with (fst (out, m)). apply in_map. exact HinL. }
  assert (Hne2 : (b - cf_head, m + cf_head) <> (out - cf_head, Z.of_nat Q + 1 + cf_head))
    by (intros E; injection E as E _; lia).
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbl Hin Hne2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rq in Hd.
  assert (Rm : req_size (m + cf_head) >= m + cf_head) by (pose proof (req_size_pos (m + cf_head)); lia). lia.
- apply Hnimg. exact (psbs_ro_img _ (proj1 (Hro a Ha))).
- apply Hnimg. exact (psbs_ro_img _ (proj1 (Hro a Ha))).
- assert (Hne2 : (b, m) <> (out - cf_head, Z.of_nat Q + 1 + cf_head)).
  { intros E. injection E as E _. apply Hnh. rewrite EHp, E. left. reflexivity. }
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR HinA Hin Hne2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rq in Hd.
  pose proof (req_size_pos m). lia.
Qed.


(* the block a stretch's own malloc added is no block of the entry state (blocks are pairwise disjoint and not empty) *)
Lemma psb_new_block : forall ly S Hp (W : world segs) mem md l b n,
  ARx ly S Hp W mem md -> 0 <= n -> ablocks B ly S = l ++ [(b, n)] -> ~ In (b, n) l.
Proof.
intros ly S Hp W mem md l b n HAR Hn E Hin.
destruct (alx_sep segs B ARx LAWS ly S Hp W mem md HAR) as [Hq _]. apply pairwise_app_l in Hq as [Hq _].
rewrite E in Hq. apply in_split in Hin as (l1 & l2 & ->).
rewrite <- app_assoc, !map_app in Hq. cbn [map app] in Hq.
pose proof (pairwise_In2 zdisjoint _ _ _ (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1)
  (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2) [] Hq eq_refl) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd. destruct (Z.eqb_spec n 0); lia.
Qed.


(* a callee-saved register across a call, from aregs_preserved *)
Ltac psb_pres HPR :=
  first [ exact (HPR 2 ltac:(unfold acallee_saved; lia)) | exact (HPR 3 ltac:(unfold acallee_saved; lia)) | exact (HPR 4 ltac:(unfold acallee_saved; lia)) | exact (HPR 8 ltac:(unfold acallee_saved; lia)) | exact (HPR 9 ltac:(unfold acallee_saved; lia)) | exact (HPR 18 ltac:(unfold acallee_saved; lia)) | exact (HPR 19 ltac:(unfold acallee_saved; lia)) | exact (HPR 20 ltac:(unfold acallee_saved; lia)) | exact (HPR 21 ltac:(unfold acallee_saved; lia)) | exact (HPR 22 ltac:(unfold acallee_saved; lia)) | exact (HPR 23 ltac:(unfold acallee_saved; lia)) | exact (HPR 24 ltac:(unfold acallee_saved; lia)) | exact (HPR 25 ltac:(unfold acallee_saved; lia)) | exact (HPR 26 ltac:(unfold acallee_saved; lia)) | exact (HPR 27 ltac:(unfold acallee_saved; lia)) ].

(* THE CALL'S KEEP: a non-allocating call (hex4, put_utf8: S' = S, the same blocks and heads, the ledger kept) from a
   stretch state of the invariant, whose footprint FP1 is a hex4 slot of the frame or bytes of out at or past w, leaves
   the invariant at the callee-saved registers and keeps the frame off FP1 *)
Lemma psb_after_call : forall CTX CW (D : ps_in) ly S Hp W regs mem md out w r Q k mdc regsc STK1 e1 FP1
    ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q -> ps_carry D ly S Hp W mem md k [] ->
  same_but_materialized md mdc ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly S Hp W mem mdc k ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  AJ (STK1 + e1) (PS_SP D + e1) FP1 ly S Hp W mem mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  0 <= STK1 -> STK1 + 144 <= STK_parse_string -> 0 <= e1 <= 48 ->
  (forall a, PS_SP D <= a < PS_SP D + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, inFP FP1 a -> (PS_SP D + 32 <= a < PS_SP D + 40) \/ (w <= a < out + Z.of_nat Q + 1)) ->
  (forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr regsc rr = getr regs rr) ->
  aregs_preserved regsc regs2 ->
  S2 = S -> Hp2 = Hp -> ablocks B ly2 S2 = ablocks B ly S ->
  LEDGER ly2 S2 Hp2 W2 mem2 ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
    (pi_most D) (pi_own D) ->
  P mem2 ->
  psb_inv D ly2 S2 Hp2 W2 regs2 mem2 md2 out w r Q /\
  (forall a, PS_SP D <= a < spZ (pi_regs D) -> ~ inFP FP1 a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q k mdc regsc STK1 e1 FP1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1
  HPRE HI HC Hsm HJ0 HJ2 HJc HSTK0 HSTK1 He1 HWIN HFP1 HRS HPR ES EHp Eab HL2 HPm2.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof HI as (_ & HAL & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & HRO & HSC &
  Hsp & H18 & H19 & H20 & H8 & H9 & Hb0 & Hb1 & HDR).
destruct HC as (HJ & HK & HSV & HSRC & HHOME & HPc).
pose proof HPRE as (((HAR0 & _ & _ & _ & _ & HstkE & _) & _) & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWINE &
  Hq0 & Hq24 & _).
pose proof HstkE as (Hal & HstkE0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HWINE as (He0 & _ & Hetop & _).
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_ly HJ) as Hlyc.
pose proof (ajx_ar HJ0) as HARm.
pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
pose proof (ajx_ar HJc) as HAR2. pose proof (ajx_hi HJc) as F1. pose proof (ajx_blk HJc) as F2.
pose proof (ajx_img HJc) as F3.
pose proof (ajx_pres HJ2) as Hpres2.
pose proof asan_consts as (C1 & _).
pose proof psb_frame as HFR.
pose proof HDR as (done0 & _ & _ & _ & _ & _ & Hw0 & _).
pose proof cf_head_nonneg as Hh0.
unfold PS_Gen.PS_SP, PS_Gen.PS_WSP, PS_Gen.PS_WSTK in *. rewrite HFR in *.
(* FP1 is no byte below the frame or the window, and none of the text, q's struct or out's written bytes *)
assert (Hsink : ~ YI16.sink_open_fp FP1).
{ intros Hs. destruct (HFP1 0 Hs) as [Hx | Hx]; [unfold spZ in *; lia|].
  destruct HAL as (_ & H4112 & _). lia. }
(* the frame and the stack above it, off FP1 *)
assert (KST : forall a, spZ (pi_regs D) - 144 <= a < 2 ^ 64 -> ~ inFP FP1 a ->
          aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha Hn. destruct (Z_lt_le_dec a (spZ (pi_regs D) - 144 + e1)) as [Hl|Hl].
  - apply HWIN; [lia | exact Hn].
  - apply F1; [unfold spZ in *; lia | lia]. }
assert (KV : forall a n v, spZ (pi_regs D) - 144 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
          (forall i, 0 <= i < Z.of_nat n -> ~ inFP FP1 (a + i)) ->
          val_mem segs (rdW W mem) a n v -> val_mem segs (rdW W2 mem2) a n v).
{ intros a n v Ha Hn Hf. apply psb_val_mem_keep. intros i Hi. apply KST; [lia | apply Hf; lia]. }
assert (Hob : out + Z.of_nat Q + 1 <= YM05.alloc_ceiling).
{ pose proof HAL as (_ & _ & _ & _ & Eabc0 & _).
  assert (Hin0 : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
    by (rewrite Eabc0; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HARc Hin0) as (_ & _ & Hc & _).
  unfold req_size in Hc. destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia. }
assert (NF : forall a, ~ (spZ (pi_regs D) - 112 <= a < spZ (pi_regs D) - 104) ->
          (a < w \/ out + Z.of_nat Q + 1 <= a) -> ~ inFP FP1 a).
{ intros a Ha Hout Hf. destruct (HFP1 a Hf) as [Hx|Hx]; lia. }
(* the ledger's harness blocks and heads at the call state *)
pose proof HAL as (Hcnt & H4112 & Hout16 & EHpc & Eabc & HLc & HVIS & HRL & HRP & HBB).
pose proof HLc as (_ & HNDc & HFAc & HPERMc).
assert (HL1 : forall b m, In (b, m) (pi_Lam D) -> In (b - cf_head, m + cf_head) (ablocks B ly S)).
{ intros b m Hin. exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFAc (b, m) (or_intror Hin)))). }
assert (HL2' : forall b m, In (b, m) (pi_Lam D) ->
          0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2).
{ intros b m Hin. rewrite Eab, EHp.
  pose proof (proj1 (Forall_forall _ _) HFAc (b, m) (or_intror Hin)) as (Hm0 & Hbl & Hhp & _). auto. }
assert (HHp2 : forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)).
{ intros h Hh. rewrite EHp in Hh. rewrite Eab.
  apply (Permutation_in h HPERMc) in Hh. apply in_map_iff in Hh as ([a0 m0] & Ea & Hin). cbn [fst] in Ea.
  pose proof (proj1 (Forall_forall _ _) HFAc (a0, m0) Hin) as (Hm0 & Hbl & _). cbn [fst snd] in Hm0, Hbl.
  exists (m0 + cf_head). split; [lia|]. rewrite <- Ea. exact Hbl. }
(* the text after the call *)
destruct (psb_src_after_call B ARx SK LAWS ZSA IMGV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pi_Lam D) (pi_text D) (pi_tb D)
  HJc HSRC ltac:(rewrite R9; exact HHOME)) as [HSRC2 HHOME2].
{ intros a Hf Ha. destruct (HFP1 a Hf) as [Hx|Hx]; [unfold spZ in *; lia|].
  apply (psb_text_out D ly S Hp W mem md out Q a HARc HAL HHOME); [rewrite R9 in Ha; clear - Ha; lia |].
  clear - Hx Hw0 Hh0. lia. }
{ exact Hsink. }
{ intros p n Hin Hnh. rewrite Eab, EHp. auto. }
{ exact HL1. }
{ exact HL2'. }
{ exact HHp2. }
rewrite R9 in HHOME2.
(* the registers *)
assert (RG : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 rr = getr regs rr).
{ intros rr Hrr. rewrite <- (HRS rr Hrr).
  cbv [In] in Hrr.
  repeat (destruct Hrr as [<-|Hrr]; [psb_pres HPR|]). destruct Hrr. }
split.
2:{ intros a Ha Hn. apply KST; [lia | exact Hn]. }
split.
{ (* the carried facts *)
  exists (k + k1). split; [exact HJ2|].
  split.
  { refine (cj_kept_trans (SK := SK) segs B PST ARx LAWS
      STK_parse_string (spZ (pi_regs D)) (STK1 + e1) (spZ (pi_regs D) - 144 + e1) [(pi_q D, pi_q D + 8)] [] FP1 []
      (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) ly S Hp W mem mdc ly2 S2 W2 mem2 md2
      (psb_kept_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK Hsm)
      (cj_kept_of_journal (SK := SK) segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [(pi_q D, pi_q D + 8)] HJc)
      HAR0 HARm _ _ _ _).
    - unfold spZ in *. lia.
    - unfold spZ in *. lia.
    - intros a Hf. exfalso. exact (inFP_nil a Hf).
    - intros a Hf. destruct (HFP1 a Hf) as [Hx|Hx]; [right; right; unfold spZ in *; lia|].
      right. left. exists (out - cf_head), (Z.of_nat Q + 1 + cf_head).
      split; [rewrite Eabc; apply in_or_app; right; left; reflexivity|].
      split.
      + assert (Hn0 : 0 <= Z.of_nat Q + 1 + cf_head) by lia.
        exact (psb_new_block ly S Hp W mem mdc (ablocks B (pi_ly D) (pi_S D)) (out - cf_head) (Z.of_nat Q + 1 + cf_head)
          HARm Hn0 Eabc).
      + unfold req_size. destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia. }
  split.
  { unfold ps_saved in HSV |- *. cbv zeta in HSV |- *. unfold PS_Gen.PS_SP in HSV |- *. rewrite ?HFR in HSV. rewrite ?HFR.
    destruct HSV as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    repeat split; (eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | | eassumption]);
      intros i Hi; apply NF; unfold spZ in *; lia. }
  split; [exact HSRC2|]. split; [exact HHOME2 | exact HPm2]. }
subst S2 Hp2.
split.
{ (* the allocator facts: out's block is a harness block, its shadow from the law *)
  split; [exact Hcnt|]. split; [exact H4112|]. split; [exact Hout16|]. split; [exact EHpc|].
  split; [rewrite Eab; exact Eabc|]. split; [exact HL2|].
  split; [|exact (conj HRL (conj HRP HBB))].
  assert (Hin : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S))
    by (rewrite Eab, Eabc; apply in_or_app; right; left; reflexivity).
  assert (Hhp : In (out - cf_head) Hp) by (rewrite EHpc; left; reflexivity).
  destruct (alx_hshadow segs B ARx LAWS ly2 S Hp W2 mem2 md2 _ _ HAR2 Hin Hhp) as [Hbs Hhu].
  assert (Rq : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
  rewrite Rq in Hbs, Hhu. replace (out - cf_head + cf_head) with out in Hbs, Hhu by lia.
  replace (Z.of_nat Q + 1 + cf_head - cf_head) with (Z.of_nat Q + 1) in Hbs, Hhu by lia.
  split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
  intros _. apply Hhu. lia. }
assert (RG' : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 rr = getr regs rr) by exact RG.
split; [split; [rewrite (RG 23%bv ltac:(cbv; tauto)); exact H23|]; split; [rewrite (RG 22%bv ltac:(cbv; tauto)); exact H22|];
  rewrite (RG 24%bv ltac:(cbv; tauto)); exact H24|].
split; [split; [rewrite (RG 3%bv ltac:(cbv; tauto)); exact H3 | rewrite (RG 4%bv ltac:(cbv; tauto)); exact H4]|].
split; [rewrite (RG 25%bv ltac:(cbv; tauto)); exact H25|].
split; [rewrite (RG 26%bv ltac:(cbv; tauto)); exact H26|].
split; [rewrite (RG 27%bv ltac:(cbv; tauto)); exact H27|].
unfold PS_Gen.PS_SP. rewrite ?HFR.
split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | | exact V24]; intros i Hi; apply NF; unfold spZ in *; lia|].
split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | | exact V16]; intros i Hi; apply NF; unfold spZ in *; lia|].
split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | | exact V8]; intros i Hi; apply NF; unfold spZ in *; lia|].
split.
{ (* in->p, in->end, in->depth: the caller's struct above the entry sp, kept; the text from the call's text *)
  destruct HPJ as (P1 & P2 & P3 & P4 & P5 & P6).
  assert (NFq : forall i, 0 <= i < 24 -> ~ inFP FP1 (pi_q D + i)) by (intros i Hi; apply NF; unfold spZ in *; lia).
  split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | | exact P1]; intros i Hi; apply NFq; lia|].
  split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | | exact P2]; intros i Hi; replace (pi_q D + 8 + i) with (pi_q D + (8 + i)) by lia; apply NFq; lia|].
  split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | | exact P3]; intros i Hi; replace (pi_q D + 16 + i) with (pi_q D + (16 + i)) by lia; apply NFq; lia|].
  split; [intros x Hx; apply (apresent_writable segs); apply Hpres2; unfold spZ in *; lia|].
  destruct P6 as (P6 & P7 & P8 & P9 & P10 & P11 & P12). split; [exact P5|]. split; [exact P6|]. split; [exact P7|].
  split; [exact P8|]. split; [exact P9|]. split; [exact (proj1 HSRC2)|]. split; [exact P11 | exact P12]. }
split.
{ intros a Hro Hno Herr.
  rewrite (F3 a (psbs_ro_img a Hro) Hno Herr (fun Hx => psb_pst_not_ro a Hx Hro) (fp_spares_closed FP1 a Hsink)).
  exact (HRO a Hro Hno Herr). }
split; [exact HSC|].
split; [rewrite (RG 2%bv ltac:(cbv; tauto)); exact Hsp|].
split; [rewrite (RG 18%bv ltac:(cbv; tauto)); exact H18|].
split; [rewrite (RG 19%bv ltac:(cbv; tauto)); exact H19|].
split; [rewrite (RG 20%bv ltac:(cbv; tauto)); exact H20|].
split; [rewrite (RG 8%bv ltac:(cbv; tauto)); exact H8|].
split; [rewrite (RG 9%bv ltac:(cbv; tauto)); exact H9|].
split; [exact Hb0|]. split; [exact Hb1|].
destruct HDR as (done & Hby & Hlen & Hdec1 & Hdec2 & Hr & Hw & Hwr & Hsc).
exists done. split; [|exact (conj Hlen (conj Hdec1 (conj Hdec2 (conj Hr (conj Hw (conj Hwr Hsc))))))].
assert (Hin : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Eabc; apply in_or_app; right; left; reflexivity).
apply (psb_garr8_keep W W2 mem mem2); [|exact Hby]. intros i Hi.
replace (out + i) with (out - cf_head + (cf_head + i)) by lia.
apply (F2 (out - cf_head) (Z.of_nat Q + 1 + cf_head)); [exact Hin | rewrite Eab; exact Hin | unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia |].
replace (out - cf_head + (cf_head + i)) with (out + i) by lia. apply NF; [|left]; lia.
Qed.


(* ---- the call sites' arithmetic and the callee premises every call needs ---- *)
Lemma psb_stk_callees : 0 <= STK_hex4 /\ STK_hex4 + 144 <= STK_parse_string /\
  0 <= STK_put_utf8 /\ STK_put_utf8 + 144 <= STK_parse_string.
Proof. vm_compute. repeat split; discriminate. Qed.
Lemma psb_mod16_4 : forall x k, x mod 16 = 0 -> (x + 4 * k) mod 4 = 0.
Proof.
intros x k H. pose proof (Z.div_mod x 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
replace (x + 4 * k) with ((4 * (x / 16) + k) * 4) by lia. apply Z.mod_mul. lia.
Qed.
Lemma psb_mod16_neg : forall e, e mod 16 = 0 -> (- (144 + e)) mod 16 = 0.
Proof.
intros e H. pose proof (Z.div_mod e 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
replace (- (144 + e)) with ((- 9 - e / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.
(* a stack byte's shadow is zero: the stack is addressable *)
Lemma psb_ra_stack : forall ly S Hp (W : world segs) mem md a n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md x HAR). lia.
Qed.
(* a frame chain reads the layout only through its top *)
Lemma psb_achain_top : forall ly ly' (rd : reader) sp v ch, ly_top ly' = ly_top ly ->
  achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch E H. unfold achain in *. rewrite E. exact H. Qed.
(* the chain from s0 = q at a call's sp (the body sp PS_SP D), at a state the carried relation reaches *)
Lemma psb_chain_at : forall CTX CW D ly S Hp W mem md k,
  ps_pre CTX CW D -> ps_carry D ly S Hp W mem md k [] ->
  exists ch, achain ly (aview segs (w_H W) mem) (PS_SP D) (pi_q D) ch.
Proof.
intros CTX CW D ly S Hp W mem md k HPRE (HJ & HK & _).
pose proof HPRE as (((_ & _ & _ & _ & _ & Hstk & _) & _) & _ & _ & _ & _ & Hqg & _).
pose proof Hstk as (_ & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof (ajx_ly HJ) as Hly. pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
destruct (ps_chain_call_offq (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D
  (aview segs (w_H W) mem) HPRE) as (ch & Hch).
- rewrite psb_s0_q. exact Hqg.
- rewrite psb_s0_q. lia.
- lia.
- intros a Ha Hq. apply K1; [unfold spZ in *; lia | lia |].
  intros (rg & [<-|[]] & Hr). cbn [fst snd] in Hr. lia.
- exists ch. rewrite psb_s0_q in Hch. apply (psb_achain_top (pi_ly D)); [exact Etop|].
  unfold PS_Gen.PS_SP. exact Hch.
Qed.
(* a 4-byte (or any) window of the text is a text the callee may read *)
Lemma psb_src_sub : forall (W : world segs) mem text tb i n,
  src_rd W mem text tb -> 0 <= i -> i + n <= Z.of_nat (length tb) -> 0 < n ->
  src_rd W mem (text + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) tb)).
Proof.
intros W mem text tb i n (HB & H4096 & Hceil & Hamr & HRA & HHU) Hi Hin Hn.
assert (Hl : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) tb))) = n)
  by (rewrite length_firstn, length_skipn; lia).
unfold src_rd. rewrite Hl. split; [|split; [lia|split; [lia|split; [|split]]]].
- intros j Hj. rewrite length_firstn, length_skipn in Hj.
  assert (Hj' : (Z.to_nat i + j < length tb)%nat) by lia.
  destruct (HB (Z.to_nat i + j)%nat Hj') as [V R].
  rewrite nth_firstn by lia. rewrite nth_skipn.
  replace (text + i + Z.of_nat j) with (text + Z.of_nat (Z.to_nat i + j)) by lia.
  replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). exact (conj V R).
- unfold amem_range in *. lia.
- apply (range_addressable_sub _ SHADOW_OFF text (Z.of_nat (length tb))); [exact HRA | lia | lia].
- intros _. apply (psbs_hull_sub _ text (Z.of_nat (length tb))); [apply HHU; lia | lia | lia | lia].
Qed.


(* ---- THE hex4 CALL (both sites: p = r + 2 / o = sp + 36 at 456, p = r + 8 / o = sp + 32 at 968): YCbqGcallW's
   aj_call_xW_sp at e1 = 48 (the window [sp, sp + 48) of parse_string's frame holds o), the kit's thex4_specX, and the
   call's keep psb_after_call; the continuation runs at the return site ret ---- *)
Lemma psb_hex4_call : forall CTX CW (D : ps_in) ly S Hp W regs mem md out w r Q k E ss ms mdc po oo ret,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q -> ps_carry D ly S Hp W mem md k [] ->
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_hex4 ->
  ms_mem ms = mem -> same_but_materialized md mdc ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly S Hp W mem mdc k ->
  (forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) rr = getr regs rr) ->
  getr (ms_regs ms) 10 = w64 (r + po) -> getr (ms_regs ms) 11 = w64 (PS_SP D + oo) ->
  getr (ms_regs ms) 1 = w64 (BASE + (PSB_OFF + ret)) ->
  0 <= po -> r + po + 4 <= pi_text D + pi_len D -> (oo = 32 \/ oo = 36) ->
  0 <= PSB_OFF + ret < 2 ^ 40 -> (PSB_OFF + ret) mod 2 = 0 ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2,
     psb_inv D ly2 S2 Hp2 W2 regs2 mem2 md2 out w r Q ->
     getr regs2 21 = getr (ms_regs ms) 21 ->
     (forall a, PS_SP D <= a < spZ (pi_regs D) -> ~ (PS_SP D + oo <= a < PS_SP D + oo + 4) ->
        aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
     match PjGrammar.hex4 (firstn 4 (rest_atR (pi_tb D) (pi_text D) (r + po))) with
     | Some h => getr regs2 10 = w64 0 /\ val_mem segs (rdW W2 mem2) (PS_SP D + oo) 4 h
     | None => getr regs2 10 = w64 (-1)
     end ->
     SRr segs W2 (cfg_at segs (psb_pc ret) regs2 mem2 md2) (ps_post CW D)) ->
  SRr segs W (mkCfg ms mdc) (ps_post CW D).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q k E ss ms mdc po oo ret HPRE HI HC HS Hrv Hpc Hmem Hsm HJ0 HRS
  H10 H11 H1 Hpo Hpo4 Hoo Hret0 Hret2 Kont.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof HI as (_ & HAL & _ & (H3 & H4) & _ & _ & _ & _ & _ & _ & _ & HRO & _ & Hsp & _ & _ & H20 & H8 & _).
pose proof HAL as (_ & _ & _ & _ & _ & HLc & _).
pose proof HC as (HJ & _ & _ & HSRC & _ & HPc).
pose proof HPRE as (((HAR0 & _ & _ & Hgp0 & Htp0 & Hstk & _) & _ & Hsp64) & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ &
  HWINE & Hq0 & Hq24 & _).
pose proof Hstk as (Hal & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HWINE as (He0 & He16 & Hetop & _).
pose proof (ajx_ar HJ0) as HARm. pose proof (ajx_ly HJ0) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
pose proof psb_stk_callees as (K0 & K1 & _).
pose proof psb_frame as HFR.
pose proof asan_consts as (C1 & _).
assert (Hspc : spZ (ms_regs ms) = PS_SP D)
  by (unfold spZ; rewrite (HRS 2%bv ltac:(cbv; tauto)), Hsp; unfold w64; rewrite unsigned_lit_small;
      [reflexivity | unfold PS_Gen.PS_SP, spZ in *; rewrite HFR; lia]).
assert (Hs0c : s0Z (ms_regs ms) = pi_q D)
  by (unfold s0Z; rewrite (HRS 8%bv ltac:(cbv; tauto)), H8; unfold w64; rewrite unsigned_lit_small; [reflexivity | unfold spZ in *; lia]).
destruct (psb_chain_at CTX CW D ly S Hp W mem md k HPRE HC) as (ch1 & Hch).
assert (HB4096 : 4096 <= BASE) by (unfold Z.le; vm_compute; discriminate).
assert (HBlo : BASE < 2 ^ 40) by (vm_compute; reflexivity).
assert (HBtop : BASE + 2 ^ 40 < 2 ^ 64) by (unfold Z.lt; vm_compute; reflexivity).
set (o := PS_SP D + oo).
set (bs := firstn 4 (rest_atR (pi_tb D) (pi_text D) (r + po))).
assert (Hbs : length bs = 4%nat)
  by (unfold bs, rest_atR; rewrite length_firstn, length_skipn; lia).
assert (Hsrc : src_rd W mem (r + po) bs).
{ pose proof (psb_src_sub W mem (pi_text D) (pi_tb D) (r + po - pi_text D) 4 HSRC ltac:(lia) ltac:(lia) ltac:(lia)) as H.
  replace (pi_text D + (r + po - pi_text D)) with (r + po) in H by lia. exact H. }
eapply SRr_bind.
{ refine (aj_call_xW_sp (SK := SK) segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) W E ss ms (PS_WSTK D) (PS_WSP D)
    [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp mdc k STK_hex4 48
    [(o, o + 4)] (- (144 + pi_e D)) (w64 (BASE + (PSB_OFF + ret))) ch1 _ HS Hrv ltac:(rewrite Hmem; exact HJ0) _ _ _ _ _ _ _ _
    _ _ H1 _ _ _ _ _).
  - rewrite Hspc. unfold PS_Gen.PS_SP, PS_Gen.PS_WSP. rewrite HFR. lia.
  - exact (psb_mod16_neg _ He16).
  - lia.
  - exact K0.
  - unfold PS_Gen.PS_WSTK. lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite (HRS 3%bv ltac:(cbv; tauto)), H3. exact Hgp0.
  - rewrite (HRS 4%bv ltac:(cbv; tauto)), H4. exact Htp0.
  - apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PSB_PAImg)); [exact Hret0 | exact Hret2].
  - unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (PS_WSP D + - (144 + pi_e D)) with (PS_SP D) by (unfold PS_Gen.PS_SP, PS_Gen.PS_WSP; rewrite HFR; lia).
    rewrite Hmem, Hs0c. apply (psb_achain_top ly); [reflexivity | exact Hch].
  - intros Hpre Hwin. rewrite Hpc. rewrite Hmem in Hpre, Hwin |- *.
    refine (HHEX4 ly S Hp W (ms_regs ms) mem mdc ch1 48 (r + po) o bs
      ((out, Z.of_nat Q + 1) :: pi_Lam D) (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1)))
      (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) _ H10 H11 Hbs Hsrc Hwin _ _ _ _ _).
    + split; [exact Hpre|]. split; [exact HRO|].
      split; [rewrite Hspc, Ehi; unfold PS_Gen.PS_SP; rewrite HFR; lia|].
      (* fpre's raZ bound, and FRM0-ENTRY's frm_zero: the entry's (the same fx; parse_string runs no float op) *)
      split; [|exact (proj2 (proj2 (proj2 (proj2 (proj1 HPRE)))))].
      unfold raZ. rewrite H1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + rewrite Hspc. unfold o. lia.
    + rewrite Hspc. unfold o. lia.
    + unfold o, PS_Gen.PS_SP. rewrite HFR. destruct Hoo as [-> | ->].
      * replace (spZ (pi_regs D) - 144 + 32) with (spZ (pi_regs D) + 4 * (-28)) by lia. exact (psb_mod16_4 _ _ Hal).
      * replace (spZ (pi_regs D) - 144 + 36) with (spZ (pi_regs D) + 4 * (-27)) by lia. exact (psb_mod16_4 _ _ Hal).
    + apply (psb_ra_stack ly S Hp W mem mdc); [exact HARm | rewrite Elo; unfold o, PS_Gen.PS_SP; rewrite HFR; unfold spZ in *; lia |
        rewrite Ehi; unfold o, PS_Gen.PS_SP; rewrite HFR; unfold spZ in *; lia].
    + exact HLc.
  - intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right. right. right.
    unfold o, PS_Gen.PS_SP, PS_Gen.PS_WSP, PS_Gen.PS_WSTK in *. rewrite HFR in *. destruct Hoo as [-> | ->]; lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HX & HP &
  ((Hroom & EHp2 & ES2 & Eab2 & HL2 & Hres) & HMN)).
rewrite Hmem in HJc, HX.
replace (PS_WSP D + - (144 + pi_e D) + 48) with (PS_SP D + 48) in HJc, HX
  by (unfold PS_Gen.PS_SP, PS_Gen.PS_WSP; rewrite HFR; lia).
replace (PS_WSP D + - (144 + pi_e D)) with (PS_SP D) in HX
  by (unfold PS_Gen.PS_SP, PS_Gen.PS_WSP; rewrite HFR; lia).
assert (He48 : 0 <= 48 <= 48) by lia.
destruct (psb_after_call CTX CW D ly S Hp W regs mem md out w r Q k mdc (ms_regs ms) STK_hex4 48 [(o, o + 4)]
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HI HC Hsm HJ0 HJ2 HJc K0 K1 He48 HX) as [HI2 HK2].
- intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. left. unfold o in Ha. destruct Hoo as [-> | ->]; lia.
- exact HRS.
- exact HP.
- exact ES2.
- exact EHp2.
- exact Eab2.
- exact HL2.
- exact (PCALL _ _ HMN HPc).
- assert (Hcfg : mkCfg (mkst regs2 (w64 (BASE + (PSB_OFF + ret))) mem2 (seg_rom segs)) md2 =
                 cfg_at segs (psb_pc ret) regs2 mem2 md2)
    by (unfold cfg_at, psb_pc; do 3 f_equal; lia).
  rewrite Hcfg. apply (Kont ly2 S2 Hp2).
  + exact HI2.
  + exact (HP 21 ltac:(unfold acallee_saved; lia)).
  + intros a Ha Hn. apply HK2; [exact Ha|]. intros (rg & [<-|[]] & Ha'). cbn [fst snd] in Ha'. unfold o in Ha'. lia.
  + fold bs. destruct (PjGrammar.hex4 bs) as [h|]; [exact Hres | exact (proj1 Hres)].
Qed.


(* ---- after a run: the registers the run left alone, the memory of a read-only run, the model ---- *)
Lemma psb_agree_ewset : forall k0 E X k w, (k0 <= k)%nat -> env_agree k0 E X -> env_agree k0 E (ewset X k w).
Proof. intros k0 E X k w Hk H. eapply env_agree_trans; [exact H|]. eapply env_agree_le; [|apply env_agree_ewset]. exact Hk. Qed.
Ltac psb_agree := repeat (apply psb_agree_ewset; [lia|]); apply env_agree_refl.
Lemma psb_ro_mem : forall E rs (m m' : word -> option byte), all_ro rs = true -> frame_of E rs m m' -> m' = m.
Proof. intros E rs m m' Hro HF. apply functional_extensionality. intros x. exact (frame_of_ro E rs m m' Hro HF x). Qed.

(* ---- THE FREE EXIT: at PSB_FREE after runs that wrote nothing, with decode refusing the text from r ---- *)
Lemma psb_free_exit : forall CTX CW (D : ps_in) ly S Hp W regs mem md out w r Q regs' md',
  psb_seg_freeP B ARx SK CTX CW P -> ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  (exists k, ps_carry D ly S Hp W mem md' k []) ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None ->
  getr regs' 2 = getr regs 2 -> getr regs' 18 = getr regs 18 -> getr regs' 8 = getr regs 8 ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  SRr segs W (cfg_at segs (psb_pc PSB_FREE) regs' mem md') (ps_post CW D).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q regs' md' FREE HPRE HI HC Hdec R2 R18 R8 R3 R4.
pose proof HI as (_ & HAL & _ & (H3 & H4) & _ & _ & _ & _ & _ & _ & HPJ & HRO & HSC & Hsp & H18 & _ & _ & H8 & _ & _ & _ & HDR).
apply ps_finP_hand. apply (FREE D ly S Hp W regs' mem md' out Q HPRE).
split; [exact HC|]. split; [exact HAL|]. split; [split; [rewrite R3; exact H3 | rewrite R4; exact H4]|].
split; [exact HPJ|]. split; [exact HRO|]. split; [exact HSC|].
split; [destruct HDR as (done & _ & _ & _ & Hn & _); exact (Hn Hdec)|].
split; [rewrite R2; exact Hsp|]. split; [rewrite R18; exact H18 | rewrite R8; exact H8].
Qed.


(* ---- STRETCH D: after put_utf8 (1044): the decode constants reloaded, the wrap check on w + len (not taken),
   w += len, j 544, the q + 8 shadow re-check (0), in->end, s4 = s5, bltu s5, end to PSB_DEC ---- *)
Definition psb_factsD : facts :=
  mkFacts [(2%nat, psb_af_sp); (42%nat, mkAF 1 4 0); (51%nat, psb_af_ptr); (53%nat, psb_af_ptr); (64%nat, psb_af_ptr)]
    [] [].
Definition psb_XD (D : ps_in) : list word := [w64 (pi_text D + pi_len D)].
Lemma psb_stD : forall CTX CW D ly S Hp W regs mem md out w r Q r' len,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 10 = w64 len -> 1 <= len <= 4 -> getr regs 21 = w64 r' -> r < r' < pi_text D + pi_len D ->
  w + len <= out + Z.of_nat Q + 1 ->
  st_ok_pi segs VAL (psb_E D regs (psb_XD D))
    (mkSS (PSB_OFF + 1044) (psb_sr (SOff 42 0) (SOff 53 0)) [psb_rg_qe; psb_rg_sh8] None psb_factsD)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + 1044))) mem (seg_rom segs))).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q r' len HPRE HI H10 Hlen H21 Hr' Hw'. unfold psb_XD.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
destruct HI as ((k & HJ & _) & HAL & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & _ & _ &
  Hsp & H18 & H19 & H20 & H8 & H9 & _ & _ & HDR).
pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
pose proof HWIN as (He0 & _ & Hetop & _).
pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Ely_top & Ely_lo & Ely_hi & _).
pose proof HPJ as (_ & Vend & _).
pose proof HAL as (_ & H4112 & _ & _ & Eab & _).
pose proof HDR as (done & _ & _ & _ & _ & _ & Hw0 & _).
assert (Hob : out + Z.of_nat Q + 1 <= YM05.alloc_ceiling).
{ assert (Hin0 : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin0) as (_ & _ & Hc & _).
  pose proof cf_head_nonneg. unfold req_size in Hc. destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia. }
assert (Vsh : val_mem segs (rdW W mem) (SHADOW_OFF + (pi_q D + 8) / 8) 1 0).
{ apply (psb_val_mem_sh0 ly S Hp W mem md); [exact HAR|]. rewrite Ely_lo, Ely_hi. unfold spZ in *. lia. }
pose proof asan_consts as (C1 & _).
pose proof cf_head_nonneg as Hh0.
assert (Hdq : 0 <= (pi_q D + 8) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold spZ in *; lia).
assert (Rcell : 0 <= SHADOW_OFF + (pi_q D + 8) / 8 < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (Rq : 0 <= pi_q D < 2 ^ 64) by (unfold spZ in *; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- psb_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; psb_region_head; rewrite ?(unsigned_lit_small _ Rcell), ?(unsigned_lit_small _ Rq).
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil. psb_chunk Vend.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil. psb_chunk Vsh.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. psb_region_head. rewrite ?(unsigned_lit_small _ Rcell), ?(unsigned_lit_small _ Rq).
  unfold SHADOW_OFF in *. repeat split; try exact I; unfold spZ in *; lia.
- split; [|split; exact I]. cbn [psb_factsD f_atoms atoms_ok].
  repeat (split; [psb_fact_tac|]). exact I.
Qed.


Lemma psb_post_reg : forall E E' ss (ms : machine_state) H rr e,
  st_ok_pi segs VAL E' ss (restrict H ms) -> env_agree 512 E E' -> sr_get (ss_regs ss) rr = e ->
  sv_atoms_lt 512 e = true -> getr (ms_regs ms) rr = sv_denot E e.
Proof.
intros E E' ss ms H rr e HS HA He Hat. rewrite (st_ok_pi_restrict_reg H E' ss ms rr HS), He.
exact (sv_denot_agree 512 E E' e HA Hat).
Qed.
(* a register of a post-run state, as an sv of the stretch's environment *)
Ltac psb_post HS E rr H :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) rr) in
    pose proof (psb_post_reg E _ ss _ _ rr e HS ltac:(psb_agree) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)) as H end.
(* YE2y.v :419-435's lxor_ones / U_not (not imported; the same text) *)
Lemma psb_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|]. apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by lia.
rewrite Z.ldiff_land.
assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma psb_U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (Z.ones 64).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite psb_lxor_ones by lia.
change (Z.ones 64) with (2 ^ 64 - 1). apply zcanon_id. unfold M64. lia.
Qed.
(* an atom of a stretch environment, as an unsigned value *)


Lemma psb_ro_mem' : forall E rs (m m' : word -> option byte), frame_of E rs m m' -> all_ro rs = true -> m' = m.
Proof. intros E rs m m' HF Hro. exact (psb_ro_mem E rs m m' Hro HF). Qed.
(* the memory of read-only runs: EM : ms_mem (current) = the stretch's memory *)
Ltac psb_mem :=
  lazymatch goal with HF : frame_of _ _ _ (ms_mem ?m1) |- _ =>
    let E2 := fresh "EMn" in
    pose proof (psb_ro_mem' _ _ _ _ HF ltac:(vm_compute; reflexivity)) as E2; clear HF;
    try (match goal with EMo : ms_mem _ = _ |- _ =>
      lazymatch EMo with E2 => fail | _ => rewrite EMo in E2; clear EMo end end);
    rename E2 into EM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac psb_sbm := repeat (first [apply same_but_materialized_refl
  | eapply same_but_materialized_trans; [|apply same_but_materialized_wvb_any]]).
(* a register of a post-run state, read off its sv in the stretch's environment *)
Ltac psb_preg HS E :=
  lazymatch goal with |- getr (ms_regs ?ms) ?rr = _ =>
    let Hx := fresh "Hx" in psb_post HS E rr Hx; rewrite Hx; clear Hx; cbn [sv_denot]; try unfold psb_XB; try unfold psb_XD;
    psb_ew;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned end.
Ltac psb_rg HS E := psb_preg HS E; first [reflexivity | assumption].
(* the write premise of a run whose regions are all read-only *)
Ltac psb_wr_ro := let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (rg & Hin & Ha); cbn [ss_mem add_cond In] in Hin;
  repeat (destruct Hin as [<-|Hin]; [cbn in Ha; lia|]); destruct Hin.

(* out's block: below the allocator ceiling *)
Lemma psb_out_bound : forall (D : ps_in) ly S Hp W regs mem md out w r Q,
  psb_inv D ly S Hp W regs mem md out w r Q -> 4096 <= out /\ out + Z.of_nat Q + 1 <= YM05.alloc_ceiling.
Proof.
intros D ly S Hp W regs mem md out w r Q ((k & HJ & _) & HAL & _).
pose proof (ajx_ar HJ) as HAR. pose proof HAL as (_ & H4112 & _ & _ & Eab & _). pose proof cf_head_nonneg as Hh0.
assert (Hin0 : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin0) as (_ & _ & Hc & _).
unfold req_size in Hc. destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia.
Qed.

Section runs.
Let RUN := @paj_run_x_m fx rc SK B_prog_listing PSB_PAListing PSB_PAImg B prh_pst ARx _ LAWS PST_ok.
Let RUNTO := @paj_run_to_x_m fx rc SK B_prog_listing PSB_PAListing PSB_PAImg B prh_pst ARx _ LAWS PST_ok.
Let BR := @paj_branch fx rc B_prog_listing PSB_PAImg.
Let RUNI := @paj_run_x_m_inv fx rc SK B_prog_listing PSB_PAListing PSB_PAImg B prh_pst ARx _ LAWS PST_ok P PLAW.
Let RUNTOI := @paj_run_to_x_m_inv fx rc SK B_prog_listing PSB_PAListing PSB_PAImg B prh_pst ARx _ LAWS PST_ok P PLAW.

Lemma psb_runD : forall CTX CW m (D : ps_in) ly S Hp W regs mem md out w r Q r' len,
  psb_dec_ltP B ARx SK CTX CW P m -> ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  ps_dec_rel D W mem out (w + len) r' Q ->
  getr regs 10 = w64 len -> 1 <= len <= 4 -> getr regs 21 = w64 r' -> r < r' ->
  (Q - Z.to_nat (r - (pi_p D + 1)) <= m)%nat ->
  SRr segs W (cfg_at segs (psb_pc 1044) regs mem md) (ps_post CW D).
Proof.
intros CTX CW m D ly S Hp W regs mem md out w r Q r' len HLT HPRE HI HDR' H10 Hlen H21 Hrr Hm.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof HDR' as (done' & _ & _ & _ & _ & Hr' & Hw' & Hwr' & _).
assert (Hre : r < r' < pi_text D + pi_len D) by lia.
assert (Hwl : w + len <= out + Z.of_nat Q + 1) by lia.
pose proof (psb_stD CTX CW D ly S Hp W regs mem md out w r Q r' len HPRE HI H10 Hlen H21 Hre Hwl) as HS.
pose proof HS as HS0.
pose proof HI as ((k & HC) & HAL & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & HRO & HSC &
  Hsp & H18 & H19 & H20 & H8 & H9 & _).
pose proof HC as (HJ & _).
pose proof (psb_env_img D regs (psb_XD D)) as HEI.
assert (SHOK : sh_ok segs PSB_Bx [] (psb_E D regs (psb_XD D)) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (psb_out_bound D ly S Hp W regs mem md out w r Q HI) as (Ho1 & Ho2).
pose proof asan_consts as (C1 & _).
assert (U42 : U (psb_E D regs (psb_XD D)) (SOff 42 0) = len)
  by (apply U_atom; [psb_ew; exact H10 | lia]).
assert (U51 : U (psb_E D regs (psb_XD D)) (SOff 51 0) = w)
  by (apply U_atom; [psb_ew; exact H19 | lia]).
assert (U53 : U (psb_E D regs (psb_XD D)) (SOff 53 0) = r')
  by (apply U_atom; [psb_ew; exact H21 | lia]).
assert (U64 : U (psb_E D regs (psb_XD D)) (SOff 64 0) = pi_text D + pi_len D)
  by (apply U_atom; [unfold psb_XD; psb_ew; reflexivity | lia]).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + 1044) with (BASE + (PSB_OFF + 1044)) by lia.
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
{ (* the wrap check on w + len: not taken *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite ?(U_agree 512 (psb_E D regs (psb_XD D))) in Hc by (first [psb_agree | reflexivity]).
  rewrite psb_U_not, U51, U42 in Hc. clear - Hc Hlen Hwl Ho2 C1 R5. lia. }
clear Hc. paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
2:{ (* s5 is below end: the closing quote is past it *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
  rewrite ?(U_agree 512 (psb_E D regs (psb_XD D))) in Hc by (first [psb_agree | reflexivity]).
  rewrite U53, U64 in Hc. clear - Hc Hre. lia. }
paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_DEC); [psb_wr_ro|]. psb_mem.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite EM.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ _ _; cfg_model := ?mdx |} _ =>
  replace (Z_to_bv 64 (BASE + _)) with (w64 (psb_pc PSB_DEC)) by (unfold w64, psb_pc; f_equal; vm_compute; reflexivity);
  change (SRr segs W (cfg_at segs (psb_pc PSB_DEC) rg mem mdx) (ps_post CW D)) end.
apply ps_finP_hand. apply (HLT D ly S Hp W _ mem _ out (w + len) r' Q HPRE).
2:{ lia. }
rewrite EM in HJ.
split; [exists k; apply (psb_carry_md D ly S Hp W mem md _ k HC HJ); psb_sbm|].
split; [exact HAL|].
split; [unfold psb_sh_regs; repeat split; psb_rg HS (psb_E D regs (psb_XD D))|].
split; [unfold ps_gptp; split; psb_rg HS (psb_E D regs (psb_XD D))|].
split; [unfold psb_dec_consts; repeat (split; [psb_rg HS (psb_E D regs (psb_XD D))|]); split; [exact V24|]; split; [exact V16 | exact V8]|].
split; [exact HPJ|]. split; [exact HRO|]. split; [exact HSC|].
split; [psb_rg HS (psb_E D regs (psb_XD D))|]. split; [psb_rg HS (psb_E D regs (psb_XD D))|].
split.
{ lazymatch goal with |- getr (ms_regs ?ms) ?rr = _ =>
    let Hx := fresh "Hx" in psb_post HS (psb_E D regs (psb_XD D)) rr Hx; rewrite Hx; clear Hx end.
  rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U42, U51.
  rewrite (Z.add_comm w len). apply zcanon_id. unfold M64. lia. }
split; [psb_rg HS (psb_E D regs (psb_XD D))|].
split; [psb_preg HS (psb_E D regs (psb_XD D)); unfold psb_XD; cbn [nth]; reflexivity|].
split; [psb_rg HS (psb_E D regs (psb_XD D))|].
split.
{ pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
  pose proof HWIN as (He0 & _ & Hetop & _).
  pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
  psb_preg HS (psb_E D regs (psb_XD D)). rewrite H8. unfold w64.
  rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
exact HDR'.
Qed.


(* ---- decode's one step at a backslash-u, over the text from a cursor (PjGrammar.decode / low / scan) ---- *)
Lemma psu_rest_split4 : forall tb text r, text <= r -> r + 4 <= text + Z.of_nat (length tb) ->
  exists d0 d1 d2 d3, rest_atR tb text r = d0 :: d1 :: d2 :: d3 :: rest_atR tb text (r + 4).
Proof.
intros tb text r Hr Hl. unfold rest_atR.
assert (E : skipn (Z.to_nat (r - text)) tb = firstn 4 (skipn (Z.to_nat (r - text)) tb) ++ skipn 4 (skipn (Z.to_nat (r - text)) tb))
  by (symmetry; apply firstn_skipn).
rewrite skipn_skipn in E. replace (4 + Z.to_nat (r - text))%nat with (Z.to_nat (r + 4 - text)) in E by lia.
assert (Hl4 : length (firstn 4 (skipn (Z.to_nat (r - text)) tb)) = 4%nat) by (rewrite length_firstn, length_skipn; lia).
destruct (firstn 4 (skipn (Z.to_nat (r - text)) tb)) as [|d0 [|d1 [|d2 [|d3 [|d4 l]]]]]; cbn in Hl4; try lia.
exists d0, d1, d2, d3. exact E.
Qed.
Lemma psu_rest_split2 : forall tb text r, text <= r -> r + 2 <= text + Z.of_nat (length tb) ->
  exists d0 d1, rest_atR tb text r = d0 :: d1 :: rest_atR tb text (r + 2).
Proof.
intros tb text r Hr Hl. unfold rest_atR.
assert (E : skipn (Z.to_nat (r - text)) tb = firstn 2 (skipn (Z.to_nat (r - text)) tb) ++ skipn 2 (skipn (Z.to_nat (r - text)) tb))
  by (symmetry; apply firstn_skipn).
rewrite skipn_skipn in E. replace (2 + Z.to_nat (r - text))%nat with (Z.to_nat (r + 2 - text)) in E by lia.
assert (Hl2 : length (firstn 2 (skipn (Z.to_nat (r - text)) tb)) = 2%nat) by (rewrite length_firstn, length_skipn; lia).
destruct (firstn 2 (skipn (Z.to_nat (r - text)) tb)) as [|d0 [|d1 [|d2 l]]]; cbn in Hl2; try lia.
exists d0, d1. exact E.
Qed.
Lemma psu_rest_at_u : forall tb text r, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 ->
  rest_atR tb text r = 92 :: 117 :: rest_atR tb text (r + 2).
Proof.
intros tb text r Hr H0 H1. rewrite (psu_rest_cons _ _ r 92) by (lia || exact H0).
rewrite (psu_rest_cons _ _ (r + 1) 117) by (lia || exact H1). do 3 f_equal. lia.
Qed.
(* fewer than four bytes after the backslash-u: decode refuses *)
Lemma psu_dec_short_at : forall tb text r, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> text + Z.of_nat (length tb) - (r + 2) < 4 ->
  PjGrammar.decode (rest_atR tb text r) = None.
Proof.
intros tb text r Hr H0 H1 Hs. rewrite (psu_rest_at_u tb text r Hr H0 H1). apply psu_dec_short.
pose proof (psu_rest_len tb text (r + 2) ltac:(lia)). lia.
Qed.
(* four or more: the four digits, then the code point's cases *)
Lemma psu_dec_u : forall tb text r, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 6 <= text + Z.of_nat (length tb) ->
  PjGrammar.decode (rest_atR tb text r) =
  match PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) with
  | None => None
  | Some cp =>
    if cp =? 0 then None
    else if (55296 <=? cp) && (cp <? 56320) then
      match rest_atR tb text (r + 6) with
      | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
        match PjGrammar.low (rest_atR tb text (r + 6)) with
        | Some lo => PjGrammar.emit (PjGrammar.utf8 (PjGrammar.pair_cp cp lo)) (PjGrammar.decode r4)
        | None => None
        end
      | _ => None
      end
    else if (56320 <=? cp) && (cp <? 57344) then None
    else PjGrammar.emit (PjGrammar.utf8 cp) (PjGrammar.decode (rest_atR tb text (r + 6)))
  end.
Proof.
intros tb text r Hr H0 H1 Hl. rewrite (psu_rest_at_u tb text r Hr H0 H1).
destruct (psu_rest_split4 tb text (r + 2) ltac:(lia) ltac:(lia)) as (d0 & d1 & d2 & d3 & E).
replace (r + 2 + 4) with (r + 6) in E by lia. rewrite E. rewrite psu_dec_u4. reflexivity.
Qed.
(* the low half after a high surrogate, at r6 = r + 6 *)
Lemma psu_low_at : forall tb text r6, text <= r6 -> nth_error tb (Z.to_nat (r6 - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r6 + 1 - text)) = Some 117 ->
  PjGrammar.low (rest_atR tb text r6) =
  match PjGrammar.hex4 (firstn 4 (rest_atR tb text (r6 + 2))) with
  | Some lo => if (56320 <=? lo) && (lo <=? 57343) then Some lo else None
  | None => None
  end.
Proof.
intros tb text r6 Hr H0 H1. rewrite (psu_rest_at_u tb text r6 Hr H0 H1). cbn [PjGrammar.low].
replace ((92 =? 92) && (117 =? 117)) with true by reflexivity. rewrite psu_hex4_firstn. reflexivity.
Qed.
Lemma psu_low_b0 : forall tb text r6 b, text <= r6 -> r6 + 2 <= text + Z.of_nat (length tb) ->
  nth_error tb (Z.to_nat (r6 - text)) = Some b -> b <> 92 -> PjGrammar.low (rest_atR tb text r6) = None.
Proof.
intros tb text r6 b Hr Hl Hb Hn. rewrite (psu_rest_cons _ _ r6 b) by (lia || exact Hb).
destruct (rest_atR tb text (r6 + 1)) as [|e0 l]; [reflexivity|].
cbn [PjGrammar.low]. rewrite (proj2 (Z.eqb_neq b 92) Hn). reflexivity.
Qed.
Lemma psu_low_b1 : forall tb text r6 b, text <= r6 -> r6 + 2 <= text + Z.of_nat (length tb) ->
  nth_error tb (Z.to_nat (r6 + 1 - text)) = Some b -> b <> 117 -> PjGrammar.low (rest_atR tb text r6) = None.
Proof.
intros tb text r6 b Hr Hl Hb Hn.
destruct (psu_rest_split2 tb text r6 ltac:(lia) ltac:(lia)) as (e0 & e1 & E).
assert (Ee1 : e1 = b).
{ pose proof (psu_rest_nth tb text r6 1 Hr ltac:(lia)) as N. rewrite E in N. cbn in N.
  replace (r6 + 1 - text) with (r6 + 1 - text) in Hb by lia. replace (Z.to_nat (r6 + 1 - text)) with (Z.to_nat (r6 + 1 - text)) in N by lia.
  rewrite Hb in N. injection N as ->. reflexivity. }
subst e1. rewrite E. cbn [PjGrammar.low]. rewrite (proj2 (Z.eqb_neq b 117) Hn), andb_false_r. reflexivity.
Qed.
(* six bytes after r6 or fewer *)
(* scan at a backslash-u with four hex digits: six bytes on *)
Lemma psu_scan_at_u : forall tb text r h, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 6 <= text + Z.of_nat (length tb) ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) = Some h ->
  PjGrammar.scan (rest_atR tb text r) = option_map (fun q => (6 + q)%nat) (PjGrammar.scan (rest_atR tb text (r + 6))).
Proof.
intros tb text r h Hr H0 H1 Hl Hh. rewrite (psu_rest_at_u tb text r Hr H0 H1).
destruct (psu_rest_split4 tb text (r + 2) ltac:(lia) ltac:(lia)) as (d0 & d1 & d2 & d3 & E).
replace (r + 2 + 4) with (r + 6) in E by lia. rewrite E in Hh |- *. rewrite psu_hex4_firstn in Hh.
exact (psu_scan_u4 d0 d1 d2 d3 _ h Hh).
Qed.
(* the length of an encoding *)
Lemma psu_utf8_len : forall c, 0 < c <= 1114111 -> (1 <= length (PjGrammar.utf8 c) <= 4)%nat.
Proof.
intros c H. unfold PjGrammar.utf8.
destruct (c <? 128); [cbn; lia|]. destruct (c <? 2048); [cbn; lia|]. destruct (c <? 65536); cbn; lia.
Qed.


(* ---- psb_at_u gives the stretch invariant, end in a0 and s5 = r + 2 ---- *)
Lemma psb_inv_of_at_u : forall D ly S Hp W regs mem md out w r Q,
  psb_at_uP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  psb_inv D ly S Hp W regs mem md out w r Q /\ getr regs 10 = w64 (pi_text D + pi_len D) /\ getr regs 21 = w64 (r + 2).
Proof.
intros D ly S Hp W regs mem md out w r Q (HC & HAL & HSH & HGT & (H25 & H26 & H27 & _ & _ & _ & _ & _ & V24 & V16 & V8) &
  HPJ & HRO & HSC & H2 & H18 & H19 & H20 & H21 & H10 & H8 & H9 & Hb0 & Hb1 & HDR).
split; [|split; [exact H10 | exact H21]].
exact (conj HC (conj HAL (conj HSH (conj HGT (conj H25 (conj H26 (conj H27 (conj V24 (conj V16 (conj V8 (conj HPJ
  (conj HRO (conj HSC (conj H2 (conj H18 (conj H19 (conj H20 (conj H8 (conj H9 (conj Hb0 (conj Hb1 HDR))))))))))))))))))))).
Qed.

(* ---- a free exit at the end of a read-only run: the state at PSB_FREE, the registers the free cut names, decode
   refusing the text from r ---- *)
Lemma psb_free_at : forall CTX CW (D : ps_in) ly S Hp W regs mem md out w r Q k E ss (ms : machine_state) mdx,
  psb_seg_freeP B ARx SK CTX CW P -> ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  ps_carry D ly S Hp W mem md k [] ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly S Hp W mem mdx k ->
  same_but_materialized md mdx ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = PSB_OFF + PSB_FREE ->
  ms_mem ms = mem ->
  getr (ms_regs ms) 2 = getr regs 2 -> getr (ms_regs ms) 18 = getr regs 18 -> getr (ms_regs ms) 8 = getr regs 8 ->
  getr (ms_regs ms) 3 = getr regs 3 -> getr (ms_regs ms) 4 = getr regs 4 ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None ->
  SRr segs W {| cfg_ms := ms; cfg_model := mdx |} (ps_post CW D).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q k E ss ms mdx FREE HPRE HI HC HJ Hsm HS Hrv Hpc EM R2 R18 R8 R3 R4 Hdec.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv). rewrite Hpc, EM.
replace (Z_to_bv 64 (BASE + (PSB_OFF + PSB_FREE))) with (w64 (psb_pc PSB_FREE)) by (unfold w64, psb_pc; f_equal; lia).
change (SRr segs W (cfg_at segs (psb_pc PSB_FREE) (ms_regs ms) mem mdx) (ps_post CW D)).
apply (psb_free_exit CTX CW D ly S Hp W regs mem md out w r Q (ms_regs ms) mdx FREE HPRE HI); try assumption.
exists k. exact (psb_carry_md D ly S Hp W mem md mdx k HC HJ Hsm).
Qed.


(* ---- THE put_utf8 CALL (1040, a0 = w, a1 = cp): YCbqGcallW's aj_call_xW_sp at e1 = 0 (put_utf8 is an fpost text:
   fpostW_x_of_apost), the kit's tput_utf8_specX, its footprint [w, w + len) inside out (the block the one malloc added),
   and the call's keep psb_after_call; the continuation runs at the return site ret ---- *)
Lemma psb_put_call : forall CTX CW (D : ps_in) ly S Hp W regs mem md out w r Q k E ss ms mdc c ret,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q -> ps_carry D ly S Hp W mem md k [] ->
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_put_utf8 ->
  ms_mem ms = mem -> same_but_materialized md mdc ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly S Hp W mem mdc k ->
  (forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) rr = getr regs rr) ->
  getr (ms_regs ms) 10 = w64 w -> getr (ms_regs ms) 11 = w64 c ->
  getr (ms_regs ms) 1 = w64 (BASE + (PSB_OFF + ret)) ->
  0 < c <= 1114111 -> w + Z.of_nat (length (PjGrammar.utf8 c)) <= out + Z.of_nat Q + 1 ->
  0 <= PSB_OFF + ret < 2 ^ 40 -> (PSB_OFF + ret) mod 2 = 0 ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2,
     psb_inv D ly2 S2 Hp2 W2 regs2 mem2 md2 out w r Q ->
     getr regs2 21 = getr (ms_regs ms) 21 ->
     getr regs2 10 = w64 (Z.of_nat (length (PjGrammar.utf8 c))) ->
     bytes_at W2 mem2 w (PjGrammar.utf8 c) ->
     SRr segs W2 (cfg_at segs (psb_pc ret) regs2 mem2 md2) (ps_post CW D)) ->
  SRr segs W (mkCfg ms mdc) (ps_post CW D).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q k E ss ms mdc c ret HPRE HI HC HS Hrv Hpc Hmem Hsm HJ0 HRS
  H10 H11 H1 Hc Hwl Hret0 Hret2 Kont.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof HI as (_ & HAL & _ & (H3 & H4) & _ & _ & _ & _ & _ & _ & _ & HRO & _ & Hsp & _ & _ & H20 & H8 & _ & _ & _ & HDR).
pose proof HAL as (_ & H4112 & _ & _ & Eab & HLc & HVIS & _).
pose proof HDR as (done0 & _ & _ & _ & _ & _ & Hw0 & _).
pose proof HC as (HJ & _ & _ & HSRC & _ & HPc).
pose proof HPRE as (((HAR0 & _ & _ & Hgp0 & Htp0 & Hstk & _) & _ & Hsp64) & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ &
  HWINE & Hq0 & Hq24 & _).
pose proof Hstk as (Hal & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HWINE as (He0 & He16 & Hetop & _).
pose proof (ajx_ar HJ0) as HARm. pose proof (ajx_ly HJ0) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
pose proof psb_stk_callees as (_ & _ & K0 & K1).
pose proof psb_frame as HFR.
pose proof asan_consts as (C1 & _).
pose proof cf_head_nonneg as Hh0.
pose proof (psu_utf8_len c Hc) as Hlen.
set (len := Z.of_nat (length (PjGrammar.utf8 c))) in *.
assert (HB4096 : 4096 <= BASE) by (unfold Z.le; vm_compute; discriminate).
assert (HBlo : BASE < 2 ^ 40) by (vm_compute; reflexivity).
assert (HBtop : BASE + 2 ^ 40 < 2 ^ 64) by (unfold Z.lt; vm_compute; reflexivity).
assert (Hspc : spZ (ms_regs ms) = PS_SP D)
  by (unfold spZ; rewrite (HRS 2%bv ltac:(cbv; tauto)), Hsp; unfold w64; rewrite unsigned_lit_small;
      [reflexivity | unfold PS_Gen.PS_SP, spZ in *; rewrite HFR; lia]).
assert (Hs0c : s0Z (ms_regs ms) = pi_q D)
  by (unfold s0Z; rewrite (HRS 8%bv ltac:(cbv; tauto)), H8; unfold w64; rewrite unsigned_lit_small; [reflexivity | unfold spZ in *; lia]).
destruct (psb_chain_at CTX CW D ly S Hp W mem md k HPRE HC) as (ch1 & Hch).
(* the block the new bytes land in *)
assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Rq : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem mdc _ _ HARm Hin_o) as (_ & H4096o & Hco & Happ & Hpres & _).
rewrite Rq in Hco, Happ, Hpres.
eapply SRr_bind.
{ refine (aj_call_xW_sp (SK := SK) segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) W E ss ms (PS_WSTK D) (PS_WSP D)
    [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp mdc k STK_put_utf8 0
    [(w, w + len)] (- (144 + pi_e D)) (w64 (BASE + (PSB_OFF + ret))) ch1 _ HS Hrv ltac:(rewrite Hmem; exact HJ0) _ _ _ _ _ _ _ _
    _ _ H1 _ _ _ _ _).
  - rewrite Hspc. unfold PS_Gen.PS_SP, PS_Gen.PS_WSP. rewrite HFR. lia.
  - exact (psb_mod16_neg _ He16).
  - lia.
  - exact K0.
  - unfold PS_Gen.PS_WSTK. lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite (HRS 3%bv ltac:(cbv; tauto)), H3. exact Hgp0.
  - rewrite (HRS 4%bv ltac:(cbv; tauto)), H4. exact Htp0.
  - apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PSB_PAImg)); [exact Hret0 | exact Hret2].
  - unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (PS_WSP D + - (144 + pi_e D)) with (PS_SP D) by (unfold PS_Gen.PS_SP, PS_Gen.PS_WSP; rewrite HFR; lia).
    rewrite Hmem, Hs0c. apply (psb_achain_top ly); [reflexivity | exact Hch].
  - intros Hpre _. rewrite Hpc. rewrite Hmem in Hpre |- *.
    eapply SRr_mono.
    { refine (HPUTU ly S Hp W (ms_regs ms) mem mdc ch1 w c
        ((out, Z.of_nat Q + 1) :: pi_Lam D) (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1)))
        (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) _ H10 H11 Hc _ _ HLc).
      - split; [exact Hpre|]. split; [exact HRO|].
        split; [rewrite Hspc, Ehi; unfold PS_Gen.PS_SP; rewrite HFR; lia|].
        split; [|exact (proj2 (proj2 (proj2 (proj2 (proj1 HPRE)))))].
        unfold raZ. rewrite H1. unfold w64. rewrite unsigned_lit_small by lia. lia.
      - exists out, (Z.of_nat Q + 1). split; [left; reflexivity|]. fold len. lia.
      - fold len. split; [lia|]. split; [lia|]. split.
        + unfold amem_range. destruct Happ as [_ [Hlow | [Hh1 Hh2]]].
          * left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
          * right. unfold kHighMemEnd in *. lia.
        + split.
          * intros a Ha. split; [|split].
            -- apply (apresent_writable segs). exact (proj1 (Hpres a ltac:(lia))).
            -- exact (proj2 (Hpres a ltac:(lia))).
            -- rewrite Hspc. unfold PS_Gen.PS_SP. rewrite HFR. unfold spZ in *. lia.
          * split.
            -- apply (range_addressable_sub _ SHADOW_OFF out (Z.of_nat Q + 1)); [exact (proj1 HVIS) | lia | lia].
            -- intros Hn. apply (psbs_hull_sub _ out (Z.of_nat Q + 1)); [apply (proj2 HVIS); lia | lia | lia | exact Hn]. }
    cbv beta. intros W3 c3 _ HP3. exact (YCbqGcallW.fpostW_x_of_apost segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ HP3).
  - intros a (rg & [<-|[]] & Hrg). cbn [fst snd] in Hrg. right. left.
    exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hin_o|].
    split.
    + assert (Hn0 : 0 <= Z.of_nat Q + 1 + cf_head) by lia.
      exact (psb_new_block ly S Hp W mem mdc (ablocks B (pi_ly D) (pi_S D)) (out - cf_head) (Z.of_nat Q + 1 + cf_head)
        HARm Hn0 Eab).
    + rewrite Rq. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HX & HP &
  ((Hroom & Ra0 & HBY & EHp2 & ES2 & Eab2 & HL2) & HMN)).
rewrite Hmem in HJc, HX.
replace (PS_WSP D + - (144 + pi_e D) + 0) with (PS_SP D + 0) in HJc, HX
  by (unfold PS_Gen.PS_SP, PS_Gen.PS_WSP; rewrite HFR; lia).
assert (He00 : 0 <= 0 <= 48) by lia.
destruct (psb_after_call CTX CW D ly S Hp W regs mem md out w r Q k mdc (ms_regs ms) STK_put_utf8 0 [(w, w + len)]
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HI HC Hsm HJ0 HJ2 HJc K0 K1 He00) as [HI2 HK2].
- intros a Ha. lia.
- intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right. lia.
- exact HRS.
- exact HP.
- exact ES2.
- exact EHp2.
- exact Eab2.
- exact HL2.
- exact (PCALL _ _ HMN HPc).
- assert (Hcfg : mkCfg (mkst regs2 (w64 (BASE + (PSB_OFF + ret))) mem2 (seg_rom segs)) md2 =
                 cfg_at segs (psb_pc ret) regs2 mem2 md2)
    by (unfold cfg_at, psb_pc; do 3 f_equal; lia).
  rewrite Hcfg. apply (Kont ly2 S2 Hp2).
  + exact HI2.
  + exact (HP 21 ltac:(unfold acallee_saved; lia)).
  + exact Ra0.
  + exact HBY.
Qed.


(* ---- decode's progress over one backslash-u escape: the encoding's bytes appended at w, the cursor at r' ---- *)
Lemma psb_dec_rel_step : forall (D : ps_in) (W : world segs) mem out w r Q r' c,
  ps_dec_rel D W mem out w r Q -> bytes_at W mem w (PjGrammar.utf8 c) ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) =
    PjGrammar.emit (PjGrammar.utf8 c) (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r')) ->
  PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) =
    option_map (fun q => (Z.to_nat (r' - r) + q)%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r')) ->
  r + Z.of_nat (length (PjGrammar.utf8 c)) <= r' ->
  ps_dec_rel D W mem out (w + Z.of_nat (length (PjGrammar.utf8 c))) r' Q.
Proof.
intros D W mem out w r Q r' c (done & Hby & Hlen & Hs & Hn & Hr & Hw & Hwr & Hsc) Hbc Hdec Hscan Hr'.
exists (done ++ PjGrammar.utf8 c).
split.
{ unfold bytes_at in *. apply garr8_app. split; [exact Hby|]. rewrite Hlen. replace (out + (w - out)) with w by lia. exact Hbc. }
split; [rewrite length_app; lia|].
split.
{ intros sx rx H. rewrite Hdec, H in Hs. specialize (Hs _ _ eq_refl). rewrite <- app_assoc. exact Hs. }
split.
{ intros H. apply Hn. rewrite Hdec, H. reflexivity. }
rewrite Hsc in Hscan.
destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r')) as [q'|] eqn:Eq; [|discriminate].
cbn [option_map] in Hscan. injection Hscan as Hscan.
split; [lia|]. split; [lia|]. split; [lia|].
f_equal. lia.
Qed.


(* ---- the arithmetic of the stretch's branch conditions (lia over 2 ^ 64 residues: the euclidean-division flag is
   on for these lemmas only) ---- *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma psu_U_sub : forall E a b, U E (SAlu ALU_ADD a (SMd M_MUL b (SLit (-1)))) = (U E a - U E b) mod 2 ^ 64.
Proof.
intros E a b. rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold M64 in Ha, Hb. lia.
Qed.
Lemma psu_U_sub_c : forall E a b c,
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL b (SLit (-1))) (SLit c)) a) = (U E a - U E b + c) mod 2 ^ 64.
Proof.
intros E a b c. rewrite !U_SAlu, U_SMd, !U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold M64 in Ha, Hb. lia.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma psu_land_m1024 : forall h, 0 <= h < 2 ^ 64 -> Z.land h (2 ^ 64 - 1024) = h / 1024 * 1024.
Proof.
intros h Hh.
replace (2 ^ 64 - 1024) with (Z.land (Z.ones 64) (Z.lnot (Z.ones 10))) by (vm_compute; reflexivity).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma psu_U_and1024 : forall E v, U E (SAlu ALU_AND v (SLit (-1024))) = U E v / 1024 * 1024.
Proof.
intros E v. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon (-1024)) with (2 ^ 64 - 1024).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite psu_land_m1024 by lia.
pose proof (Z.mul_div_le (U E v) 1024 ltac:(lia)). pose proof (Z.div_pos (U E v) 1024 ltac:(lia) ltac:(lia)).
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* the surrogate tests: the code point's top six bits *)
Lemma psu_hi_test : forall h, 0 <= h < 65536 -> (h / 1024 * 1024 =? 55296) = (55296 <=? h) && (h <? 56320).
Proof.
intros h Hh. pose proof (Z.div_mod h 1024 ltac:(lia)) as Ed. pose proof (Z.mod_pos_bound h 1024 ltac:(lia)) as Em.
destruct (Z.eqb_spec (h / 1024 * 1024) 55296), (Z.leb_spec 55296 h), (Z.ltb_spec h 56320); cbn; try reflexivity; lia.
Qed.
Lemma psu_lo_test : forall h, 0 <= h < 65536 -> (h / 1024 * 1024 =? 56320) = (56320 <=? h) && (h <? 57344).
Proof.
intros h Hh. pose proof (Z.div_mod h 1024 ltac:(lia)) as Ed. pose proof (Z.mod_pos_bound h 1024 ltac:(lia)) as Em.
destruct (Z.eqb_spec (h / 1024 * 1024) 56320), (Z.leb_spec 56320 h), (Z.ltb_spec h 57344); cbn; try reflexivity; lia.
Qed.


(* ---- the stretch after the second hex4 (972): a0 = 0, the high half h at sp + 36 (atom 65), the low half lo at
   sp + 32 (atom 66), the frame's word sp + 36 writable (the pair's store at 1028), s5 = r + 6 ---- *)
Definition psb_factsC : facts :=
  mkFacts [(2%nat, psb_af_sp); (52%nat, psb_af_ptr); (42%nat, mkAF 0 0 0); (65%nat, mkAF 55296 56319 0);
           (66%nat, mkAF 0 65535 0); (64%nat, psb_af_ptr)] [] [].
Definition psb_XC (D : ps_in) (h lo : Z) : list word := [w64 (pi_text D + pi_len D); w64 h; w64 lo].
Lemma psb_stC : forall CTX CW D ly S Hp W regs mem md out w r Q h lo,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 10 = w64 0 -> getr regs 21 = w64 (r + 6) ->
  val_mem segs (rdW W mem) (PS_SP D + 36) 4 h -> 55296 <= h < 56320 ->
  val_mem segs (rdW W mem) (PS_SP D + 32) 4 lo -> 0 <= lo < 65536 ->
  st_ok_pi segs VAL (psb_E D regs (psb_XC D h lo))
    (mkSS (PSB_OFF + 972) (psb_sr (SLit 0) (SOff 52 6))
       [psb_rg_frame (-108) (-104) [psb_hslot (-108) 65; psb_hslot (-112) 66]; psb_rg_qe; psb_rg_sh8] None psb_factsC)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + 972))) mem (seg_rom segs))).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q h lo HPRE HI H10 H21 Hh Hh0 Hlo Hlo0. unfold psb_XC.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
destruct HI as ((k & HJ & _) & _ & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & _ & _ &
  Hsp & H18 & H19 & H20 & H8 & H9 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
pose proof HWIN as (He0 & _ & Hetop & _).
pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly.
pose proof (ajx_pres HJ) as Hpres.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Ely_top & Ely_lo & Ely_hi & _).
pose proof psb_stk_callees as (K0 & K1 & _).
pose proof (psu_val_mem_mod _ _ _ _ V8) as V8'. change ((-56613888) mod 2 ^ 64) with 18446744073652937728 in V8'.
pose proof HPJ as (_ & Vend & _).
assert (Vsh : val_mem segs (rdW W mem) (SHADOW_OFF + (pi_q D + 8) / 8) 1 0).
{ apply (psb_val_mem_sh0 ly S Hp W mem md); [exact HAR|]. rewrite Ely_lo, Ely_hi. unfold spZ in *. lia. }
pose proof asan_consts as (C1 & _).
assert (Hdq : 0 <= (pi_q D + 8) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold spZ in *; lia).
assert (Rcell : 0 <= SHADOW_OFF + (pi_q D + 8) / 8 < 2 ^ 64) by (unfold SHADOW_OFF; lia).
assert (Rq : 0 <= pi_q D < 2 ^ 64) by (unfold spZ in *; lia).
unfold PS_Gen.PS_WSP, PS_Gen.PS_WSTK in Hpres.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- psb_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; psb_region_head; rewrite ?(unsigned_lit_small _ Rcell), ?(unsigned_lit_small _ Rq).
  + split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable segs); apply Hpres; unfold spZ in *; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
      [psb_chunk Hh | psb_chunk Hlo | psb_chunk V24 | psb_chunk V16 | psb_chunk V8'].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil. psb_chunk Vend.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil. psb_chunk Vsh.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. psb_region_head. rewrite ?(unsigned_lit_small _ Rcell), ?(unsigned_lit_small _ Rq).
  unfold SHADOW_OFF in *. repeat split; try exact I; lia.
- split; [|split; exact I]. cbn [psb_factsC f_atoms atoms_ok].
  repeat (split; [psb_fact_tac|]). exact I.
Qed.

(* ---- a stretch whose a0 is a literal (hex4's -1) and no region: the bnez to PSB_FREE ---- *)
Definition psb_factsN : facts := mkFacts [(2%nat, psb_af_sp); (52%nat, psb_af_ptr)] [] [].
Lemma psb_stN : forall CTX CW D ly S Hp W regs mem md out w r Q pc v s5o,
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 10 = w64 v -> getr regs 21 = w64 (r + s5o) ->
  st_ok_pi segs VAL (psb_E D regs []) (mkSS (PSB_OFF + pc) (psb_sr (SLit v) (SOff 52 s5o)) [] None psb_factsN)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + pc))) mem (seg_rom segs))).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q pc v s5o HPRE HI H10 H21.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
destruct HI as (_ & _ & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & _ & _ & _ & _ & _ & _ & Hsp & H18 & H19 & H20 &
  H8 & H9 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
pose proof HWIN as (He0 & _ & Hetop & _).
pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- psb_regs_ok.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [|split; exact I]. cbn [psb_factsN f_atoms atoms_ok].
  split; [psb_fact_tac|]. split; [psb_fact_tac|exact I].
Qed.


Ltac psb_run_w RUN HS HJ SHOK HPM Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch goal with |- SRr _ _ _ ?QQ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let Hchk := fresh "Hchk" in
assert (Hchk : sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true) by (vm_compute; reflexivity);
let HK := fresh "HK" in
assert (HK : (A_LIM <= K)%nat) by (unfold A_LIM; cbn; lia);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "psb_run_w: no hypothesis  img_env _ _ E" end in
refine (RUN W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QQ HK HEI HS SHOK Hchk Hrun HJ HPM _ _ _);
[ clear Hrun Hchk HK; cbn [sh_obls]; srr_obls
| clear Hrun Hchk HK
| clear Hrun Hchk HK HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok_inv HS HJ SHOK HPM ]
end end end end
| _ => fail "psb_run_w: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac psb_run_to_w RUNTO HS HJ SHOK HPM Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch goal with |- SRr _ _ _ ?QQ =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let Hchk := fresh "Hchk" in
assert (Hchk : sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true) by (vm_compute; reflexivity);
let HK := fresh "HK" in
assert (HK : (A_LIM <= K)%nat) by (unfold A_LIM; cbn; lia);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "psb_run_to_w: no hypothesis  img_env _ _ E" end in
refine (RUNTO W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QQ HK HEI HS SHOK Hchk Hrun HJ HPM _ _ _);
[ clear Hrun Hchk HK; cbn [sh_obls]; srr_obls
| clear Hrun Hchk HK
| clear Hrun Hchk HK HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tok_inv HS HJ SHOK HPM ]
end end end end
| _ => fail "psb_run_to_w: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.

(* a write of the frame window [sp - 144, sp): inside parse_string's own STK window *)
Lemma psb_wr_frame_ok : forall (D : ps_in) FP bl0 blc ly own a, 0 <= pi_e D ->
  spZ (pi_regs D) - 144 <= a < spZ (pi_regs D) ->
  awr_byte (PS_WSTK D) (PS_WSP D) FP bl0 blc ly own a \/ Exists (in_zr a) PST.
Proof.
intros D FP bl0 blc ly own a He Ha. left. left. pose proof psb_stk_callees as (K0 & K1 & _).
unfold PS_Gen.PS_WSP, PS_Gen.PS_WSTK. lia.
Qed.
Ltac psb_wr_fr HE0 := let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (rg & Hin & Ha); cbn [ss_mem add_cond In] in Hin;
  repeat (destruct Hin as [<-|Hin];
    [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi psb_rg_frame psb_rg_qe psb_rg_sh8 psb_rg_t67] in Ha;
     first [lia | (rewrite (psb_ew_lo _ _ _ 2 2 eq_refl) in Ha; apply (psb_wr_frame_ok _ _ _ _ _ _ a HE0); unfold spZ; lia)]|]);
  destruct Hin.


(* ---- a stretch's own store into its frame word sp + 36 (the pair's sw at 1028, the engine's write window [sp + 36,
   sp + 40)): every fact of the invariant is off that word, so it holds at the stored memory; the kept relation
   composes (YCbqGcallW's cj_kept_exec over the frame [sp - 144, sp) with cj_kept_trans) ---- *)
Lemma psb_hull_keep : forall (rd rd' : reader) x n,
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros rd rd' x n Heq H s Hs. rewrite (Heq s Hs). exact (H s Hs). Qed.
Lemma psb_inv_store : forall CTX CW (D : ps_in) ly S Hp W regs mem md out w r Q k mem' md',
  ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q -> ps_carry D ly S Hp W mem md k [] ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
    ly S Hp W mem' md' k ->
  same_but_materialized md md' ->
  (forall x : word, ~ (PS_SP D + 36 <= bv_unsigned x < PS_SP D + 40) -> rdW W mem' x = rdW W mem x) ->
  P mem' ->
  psb_inv D ly S Hp W regs mem' md' out w r Q /\ ps_carry D ly S Hp W mem' md' k [].
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q k mem' md' HPRE HI HC HJ' Hsm HFR' HPm'.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof (psb_out_bound D ly S Hp W regs mem md out w r Q HI) as (Ho1 & Ho2).
destruct HI as (_ & HAL & HSH & HGT & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & HRO & HSC & Hsp & H18 & H19 & H20 & H8 &
  H9 & Hb0 & Hb1 & HDR).
destruct HC as (HJ & HK & HSV & HSRC & HHOME & HPc).
pose proof HPRE as (((HAR0 & _ & _ & _ & _ & Hstk & _) & _) & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWINE & Hq0 &
  Hq24 & _).
pose proof Hstk as (Hal & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HWINE as (He0 & _ & Hetop & _).
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
pose proof (ajx_pres HJ') as Hpres'.
pose proof psb_frame as HFR.
pose proof psb_stk_callees as (K0 & K1 & _).
pose proof asan_consts as (C1 & _).
pose proof cf_head_nonneg as Hh0.
unfold PS_Gen.PS_SP, PS_Gen.PS_WSP, PS_Gen.PS_WSTK in *. rewrite HFR in *.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (pi_regs D) - 108 <= a < spZ (pi_regs D) - 104) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
{ intros a Ha Hn. apply aview_eq_of. apply HFR'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
assert (KV : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
          (a + Z.of_nat n <= spZ (pi_regs D) - 108 \/ spZ (pi_regs D) - 104 <= a) ->
          val_mem segs (rdW W mem) a n v -> val_mem segs (rdW W mem') a n v).
{ intros a n v Ha Hn Hw. apply psb_val_mem_keep. intros i Hi. apply KEEP; lia. }
(* below the stack: the heap, the text, the image, every shadow byte *)
assert (KLOW : forall a, 0 <= a < ly_stk_lo ly -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a)
  by (intros a Ha; apply KEEP; unfold spZ in *; lia).
assert (Hshb : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x /\ shadow_addr x + 16 <= ly_stk_lo ly).
{ intros x Hx. unfold shadow_addr. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF in *. unfold spZ in *. lia. }
assert (HSR : forall a n, 0 <= a -> a + n <= 2 ^ 47 ->
          range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n ->
          range_addressable (aview segs (w_H W) mem') SHADOW_OFF a n).
{ intros a n Ha Hn H.
  refine (range_addressable_agree (aview segs (w_H W) mem) (aview segs (w_H W) mem') SHADOW_OFF a n _ H).
  intros x Hx. apply KLOW. pose proof (Hshb x ltac:(lia)) as Hs. unfold shadow_addr in Hs. unfold shadow_of_addr. lia. }
assert (HHU : forall a n, 0 <= a -> 0 < n -> a + n <= 2 ^ 47 ->
          shadow_hull_vis (aview segs (w_H W) mem) a n -> shadow_hull_vis (aview segs (w_H W) mem') a n).
{ intros a n Ha Hn Hn2 H. apply (psb_hull_keep (aview segs (w_H W) mem)); [|exact H].
  intros s Hs. apply KLOW. pose proof (Hshb a ltac:(lia)). pose proof (Hshb (a + n - 1) ltac:(lia)).
  pose proof (Z.mul_div_le (shadow_addr a) 8 ltac:(lia)).
  pose proof (Z.mul_div_le (shadow_addr (a + n - 1)) 8 ltac:(lia)).
  pose proof (Z.div_pos (shadow_addr a) 8 ltac:(lia) ltac:(lia)).
  lia. }
assert (HGA : forall a l, 0 <= a -> a + Z.of_nat (length l) <= ly_stk_lo ly ->
          garr8 segs (rdW W mem) a l -> garr8 segs (rdW W mem') a l).
{ intros a l Ha Hl H. apply (psb_garr8_keep W W mem mem'); [|exact H]. intros i Hi. apply KLOW. lia. }
assert (HK' : cj_kept (SK := SK) segs B PST STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
          (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem' md').
{ refine (cj_kept_trans (SK := SK) segs B PST ARx LAWS STK_parse_string (spZ (pi_regs D)) 144 (spZ (pi_regs D))
    [(pi_q D, pi_q D + 8)] [] [] [] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) ly S Hp W mem md
    ly S W mem' md' HK _ HAR0 HARc _ _ _ _).
  - refine (cj_kept_exec (SK := SK) segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) 144 (spZ (pi_regs D))
      [(pi_q D, pi_q D + 8)] [] ly S Hp W mem md mem' md' (fun a => spZ (pi_regs D) - 108 <= a < spZ (pi_regs D) - 104)
      HARc _ _ _ _ _ Hsm).
    + unfold spZ in *. lia.
    + unfold spZ in *. lia.
    + unfold spZ in *. lia.
    + intros x Hx. apply HFR'. unfold spZ in *. lia.
    + intros a Ha. left. lia.
  - unfold spZ in *. lia.
  - lia.
  - intros a Hf. exfalso. exact (inFP_nil a Hf).
  - intros a Hf. exfalso. exact (inFP_nil a Hf). }
assert (HC' : ps_carry D ly S Hp W mem' md' k []).
{ split; [exact HJ'|]. split; [exact HK'|].
  split.
  { unfold ps_saved in HSV |- *. cbv zeta in HSV |- *. unfold PS_Gen.PS_SP in HSV |- *. rewrite ?HFR in HSV. rewrite ?HFR.
    destruct HSV as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    repeat split; (eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | unfold spZ in *; lia | eassumption]). }
  split; [|exact (conj HHOME HPm')].
  destruct HSRC as (HB & H4096 & Hcl & Hamr & HRA & HHV).
  split; [apply HGA; [lia | unfold spZ in *; lia | exact HB]|].
  split; [exact H4096|]. split; [exact Hcl|]. split; [exact Hamr|].
  split; [apply HSR; [lia | lia | exact HRA]|].
  intros Hn. apply HHU; [lia | exact Hn | lia | exact (HHV Hn)]. }
split; [|exact HC'].
split; [exists k; exact HC'|].
split.
{ destruct HAL as (Hcnt & H4112 & Hout16 & EHpc & Eabc & HLc & HVIS & HRL & HRP & HBB).
  split; [exact Hcnt|]. split; [exact H4112|]. split; [exact Hout16|]. split; [exact EHpc|]. split; [exact Eabc|].
  split.
  { destruct HLc as (HG & HND & HFA & HPERM). split; [|split; [exact HND|split; [|exact HPERM]]].
    - destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & G8).
      assert (KI : forall a n v, In (a, Z.of_nat n) PST ->
        val_mem segs (rdW W mem) a n v -> val_mem segs (rdW W mem') a n v).
      { intros a n v Hin Hv. refine (psb_val_mem_keep W W mem mem' a n v _ Hv). intros i Hi.
        assert (Hz : Exists (in_zr (a + i)) PST) by (apply Exists_exists; exists (a, Z.of_nat n); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
        pose proof (@pa_segs_low _ _ PSB_PAImg (a + i) (proj1 (PST_ok (a + i) Hz))) as Hl.
        apply KEEP; unfold kLowMemEnd, spZ in *; lia. }
      split; [refine (KI _ _ _ _ G1); unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right])|].
      split; [refine (KI _ _ _ _ G2); unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right])|].
      split; [refine (KI _ _ _ _ G3); unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right])|].
      split; [refine (KI _ _ _ _ G4); unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right])|].
      split; [refine (KI _ _ _ _ G5); unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right])|].
      (* the #102 cells g_most / g_own_ran_out (prh_glob's prh_most / prh_own) *)
      split; [split; [refine (KI _ _ _ _ G6); unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right]) | exact G6r]|].
      split; [split; [refine (KI _ _ _ _ G7); unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right]) | exact G7r]|].
      exact G8.
    - apply Forall_forall. intros [a m] Hin. pose proof (proj1 (Forall_forall _ _) HFA (a, m) Hin) as (Hm0 & Hbl & Hhp & Hal16 & Hv).
      split; [exact Hm0|]. split; [exact Hbl|]. split; [exact Hhp|]. split; [exact Hal16|].
      destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HARc Hbl) as (_ & H4096b & Hcb & _).
      pose proof (req_size_pos (m + cf_head)).
      cbn [fst snd] in *. assert (Hq1 : 0 <= a - cf_head) by lia.
      assert (Hq2 : a - cf_head + Z.of_nat 8 <= 2 ^ 64) by (unfold spZ in *; cbn; lia).
      assert (Hq3 : a - cf_head + Z.of_nat 8 <= spZ (pi_regs D) - 108 \/ spZ (pi_regs D) - 104 <= a - cf_head)
        by (left; specialize (H ltac:(lia)); unfold spZ in *; cbn; lia).
      exact (KV _ _ _ Hq1 Hq2 Hq3 Hv). }
  split; [|exact (conj HRL (conj HRP HBB))].
  destruct HVIS as (HVR & HVH). split; [apply HSR; [lia | lia | exact HVR]|].
  intros Hn. apply HHU; [lia | exact Hn | lia | exact (HVH Hn)]. }
split; [exact HSH|]. split; [exact HGT|]. split; [exact H25|]. split; [exact H26|]. split; [exact H27|].
unfold PS_Gen.PS_SP. rewrite ?HFR.
split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | left; unfold spZ in *; lia | exact V24]|].
split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | left; unfold spZ in *; lia | exact V16]|].
split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | left; unfold spZ in *; lia | exact V8]|].
split.
{ destruct HPJ as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
  split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | right; unfold spZ in *; lia | exact P1]|].
  split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | right; unfold spZ in *; lia | exact P2]|].
  split; [eapply KV; [unfold spZ in *; lia | unfold spZ in *; lia | right; unfold spZ in *; lia | exact P3]|].
  split; [intros x Hx; apply (apresent_writable segs); apply Hpres'; unfold spZ in *; lia|].
  split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
  split; [apply HGA; [lia | unfold spZ in *; lia | exact P10]|]. split; [exact P11 | exact P12]. }
split.
{ intros a Hro Hno Herr. rewrite (KEEP a).
  - exact (HRO a Hro Hno Herr).
  - pose proof (@pa_segs_low _ _ PSB_PAImg a (psbs_ro_img a Hro)). unfold kLowMemEnd in *. lia.
  - pose proof (@pa_segs_low _ _ PSB_PAImg a (psbs_ro_img a Hro)). unfold kLowMemEnd, spZ in *. lia. }
split; [exact HSC|]. split; [exact Hsp|]. split; [exact H18|]. split; [exact H19|]. split; [exact H20|].
split; [exact H8|]. split; [exact H9|]. split; [exact Hb0|]. split; [exact Hb1|].
destruct HDR as (done & Hby & Hlen & Hdec1 & Hdec2 & Hr & Hw & Hwr & Hsc).
exists done. split; [|exact (conj Hlen (conj Hdec1 (conj Hdec2 (conj Hr (conj Hw (conj Hwr Hsc))))))].
apply HGA; [lia | | exact Hby]. unfold spZ in *. lia.
Qed.


(* ---- more arithmetic of the \u stretch: the pair's code point, the low-half test as the engine folds it ---- *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma psu_U_pair : forall E a b,
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL a (SLit 10)) (SLit (-56613888))) b) =
  (U E a * 1024 - 56613888 + U E b) mod 2 ^ 64.
Proof.
intros E a b. rewrite !U_SAlu, !U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 10) 63) with 10.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 10) with 1024. unfold zcanon, M64.
pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold M64 in Ha, Hb. lia.
Qed.
Lemma psu_low_test2 : forall lo, 0 <= lo < 65536 ->
  (((lo + -57344) mod 2 ^ 64) <? 18446744073709550592) = negb ((56320 <=? lo) && (lo <=? 57343)).
Proof.
intros lo Hlo. destruct (Z.leb_spec 56320 lo), (Z.leb_spec lo 57343); cbn [andb negb];
  first [apply Z.ltb_ge | apply Z.ltb_lt]; lia.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma psu_U_off : forall E n c v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
intros E n c v H Hv. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* a register of a call state (st_ok), read off its sv in the stretch's environment *)
Lemma psb_call_reg : forall E E' ss (ms : machine_state) H rr e,
  st_ok segs E' ss (restrict H ms) -> env_agree 512 E E' -> sr_get (ss_regs ss) rr = e ->
  sv_atoms_lt 512 e = true -> getr (ms_regs ms) rr = sv_denot E e.
Proof.
intros E E' ss ms H rr e HS HA He Hat. pose proof (st_ok_reg _ _ _ _ rr HS) as Hr. cbn [restrict ms_regs] in Hr. rewrite Hr, He.
exact (sv_denot_agree 512 E E' e HA Hat).
Qed.
Ltac psb_cpost HS E rr Hx :=
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) rr) in
    pose proof (psb_call_reg E _ ss _ _ rr e HS ltac:(psb_agree) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)) as Hx end.
(* the callee-saved registers of a call state, against the stretch's start file *)
Ltac psb_crs HS E :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  intros rr Hrr; cbv [In] in Hrr;
  repeat (destruct Hrr as [<-|Hrr];
    [lazymatch goal with |- getr (ms_regs ?ms) ?x = _ =>
       let Hx := fresh "Hx" in psb_cpost HS E x Hx; rewrite Hx; clear Hx; cbn [sv_denot]; psb_ew;
       rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
       first [ reflexivity
             | match goal with H : getr ?rg ?r1 = getr _ ?r1 |- _ = getr ?rg ?r1 => symmetry; exact H end
             | match goal with H : getr ?rg ?r1 = w64 _ |- _ = getr ?rg ?r1 => rewrite H; reflexivity end
             | idtac ] end|]);
  try destruct Hrr.


(* ---- decode at a high surrogate (the digits at r + 2 give 55296 <= h < 56320): the low half's six bytes at r + 6 ---- *)
Lemma psu_dec_hi : forall tb text r h, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 6 <= text + Z.of_nat (length tb) ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) = Some h -> 55296 <= h < 56320 ->
  PjGrammar.decode (rest_atR tb text r) =
  if r + 12 <=? text + Z.of_nat (length tb) then
    match PjGrammar.low (rest_atR tb text (r + 6)) with
    | Some lo => PjGrammar.emit (PjGrammar.utf8 (PjGrammar.pair_cp h lo)) (PjGrammar.decode (rest_atR tb text (r + 12)))
    | None => None
    end
  else None.
Proof.
intros tb text r h Hr H0 H1 Hl Hh Hhr. rewrite (psu_dec_u tb text r Hr H0 H1 Hl), Hh.
replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace ((55296 <=? h) && (h <? 56320)) with true
  by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
destruct (Z.leb_spec (r + 12) (text + Z.of_nat (length tb))) as [H12|H12].
- destruct (psu_rest_split4 tb text (r + 6) ltac:(lia) ltac:(lia)) as (d0 & d1 & d2 & d3 & E1).
  replace (r + 6 + 4) with (r + 10) in E1 by lia.
  destruct (psu_rest_split2 tb text (r + 10) ltac:(lia) ltac:(lia)) as (d4 & d5 & E2).
  replace (r + 10 + 2) with (r + 12) in E2 by lia.
  rewrite E1, E2. reflexivity.
- pose proof (psu_rest_len tb text (r + 6) ltac:(lia)) as HL.
  destruct (rest_atR tb text (r + 6)) as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 l]]]]]]; cbn [length] in HL; try reflexivity; lia.
Qed.
(* the low half proper: four digits in [56320, 57344) *)
Lemma psu_dec_pair : forall tb text r h lo, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 12 <= text + Z.of_nat (length tb) ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) = Some h -> 55296 <= h < 56320 ->
  nth_error tb (Z.to_nat (r + 6 - text)) = Some 92 -> nth_error tb (Z.to_nat (r + 7 - text)) = Some 117 ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 8))) = Some lo ->
  PjGrammar.decode (rest_atR tb text r) =
  if (56320 <=? lo) && (lo <=? 57343)
  then PjGrammar.emit (PjGrammar.utf8 (PjGrammar.pair_cp h lo)) (PjGrammar.decode (rest_atR tb text (r + 12)))
  else None.
Proof.
intros tb text r h lo Hr H0 H1 Hl Hh Hhr H6 H7 Hlo. rewrite (psu_dec_hi tb text r h Hr H0 H1 ltac:(lia) Hh Hhr).
replace (r + 12 <=? text + Z.of_nat (length tb)) with true by (symmetry; apply Z.leb_le; lia).
rewrite (psu_low_at tb text (r + 6) ltac:(lia) H6 ltac:(replace (r + 6 + 1 - text) with (r + 7 - text) by lia; exact H7)).
replace (r + 6 + 2) with (r + 8) by lia. rewrite Hlo.
destruct ((56320 <=? lo) && (lo <=? 57343)); reflexivity.
Qed.
Lemma psu_dec_lo_none : forall tb text r h, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 12 <= text + Z.of_nat (length tb) ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) = Some h -> 55296 <= h < 56320 ->
  PjGrammar.low (rest_atR tb text (r + 6)) = None -> PjGrammar.decode (rest_atR tb text r) = None.
Proof.
intros tb text r h Hr H0 H1 Hl Hh Hhr HN. rewrite (psu_dec_hi tb text r h Hr H0 H1 ltac:(lia) Hh Hhr), HN.
destruct (r + 12 <=? text + Z.of_nat (length tb)); reflexivity.
Qed.
(* scan over the pair's twelve bytes *)
Lemma psu_scan_pair : forall tb text r h lo, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 12 <= text + Z.of_nat (length tb) ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) = Some h ->
  nth_error tb (Z.to_nat (r + 6 - text)) = Some 92 -> nth_error tb (Z.to_nat (r + 7 - text)) = Some 117 ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 8))) = Some lo ->
  PjGrammar.scan (rest_atR tb text r) =
    option_map (fun q => (Z.to_nat (r + 12 - r) + q)%nat) (PjGrammar.scan (rest_atR tb text (r + 12))).
Proof.
intros tb text r h lo Hr H0 H1 Hl Hh H6 H7 Hlo.
rewrite (psu_scan_at_u tb text r h Hr H0 H1 ltac:(lia) Hh).
rewrite (psu_scan_at_u tb text (r + 6) lo ltac:(lia) H6 ltac:(replace (r + 6 + 1 - text) with (r + 7 - text) by lia; exact H7)
  ltac:(lia) ltac:(replace (r + 6 + 2) with (r + 8) by lia; exact Hlo)).
replace (r + 6 + 6) with (r + 12) by lia. replace (Z.to_nat (r + 12 - r)) with 12%nat by lia.
destruct (PjGrammar.scan (rest_atR tb text (r + 12))); reflexivity.
Qed.
(* the BMP code point: emit, six bytes on *)
Lemma psu_dec_bmp : forall tb text r h, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 6 <= text + Z.of_nat (length tb) ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) = Some h -> h <> 0 ->
  ~ (55296 <= h < 56320) -> ~ (56320 <= h < 57344) ->
  PjGrammar.decode (rest_atR tb text r) =
    PjGrammar.emit (PjGrammar.utf8 h) (PjGrammar.decode (rest_atR tb text (r + 6))).
Proof.
intros tb text r h Hr H0 H1 Hl Hh Hn0 Hn1 Hn2. rewrite (psu_dec_u tb text r Hr H0 H1 Hl), Hh.
replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace ((55296 <=? h) && (h <? 56320)) with false
  by (symmetry; destruct (Z.leb_spec 55296 h), (Z.ltb_spec h 56320); cbn; [lia | reflexivity ..]).
replace ((56320 <=? h) && (h <? 57344)) with false
  by (symmetry; destruct (Z.leb_spec 56320 h), (Z.ltb_spec h 57344); cbn; [lia | reflexivity ..]).
reflexivity.
Qed.
Lemma psu_scan6 : forall tb text r h, text <= r -> nth_error tb (Z.to_nat (r - text)) = Some 92 ->
  nth_error tb (Z.to_nat (r + 1 - text)) = Some 117 -> r + 6 <= text + Z.of_nat (length tb) ->
  PjGrammar.hex4 (firstn 4 (rest_atR tb text (r + 2))) = Some h ->
  PjGrammar.scan (rest_atR tb text r) =
    option_map (fun q => (Z.to_nat (r + 6 - r) + q)%nat) (PjGrammar.scan (rest_atR tb text (r + 6))).
Proof.
intros tb text r h Hr H0 H1 Hl Hh. rewrite (psu_scan_at_u tb text r h Hr H0 H1 Hl Hh).
replace (Z.to_nat (r + 6 - r)) with 6%nat by lia. reflexivity.
Qed.


(* the five registers the free cut reads, at a post-run state, against the stretch's start file *)
Ltac psb_free_reg HS E :=
  psb_preg HS E;
  first [ reflexivity
        | match goal with H : getr ?rg ?r1 = getr _ ?r1 |- _ = getr ?rg ?r1 => rewrite H; reflexivity end
        | match goal with H : getr ?rg 2 = w64 _ |- _ = getr ?rg 2 =>
            rewrite H; unfold w64, PS_Gen.PS_SP, spZ; rewrite psb_frame; f_equal; lia end ].
Ltac psb_free_tac FREE HPRE HI HC HJ HS E :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?ms; cfg_model := ?mdx |} _ =>
  refine (psb_free_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ms mdx FREE HPRE HI HC HJ _ HS eq_refl ltac:(vm_compute; reflexivity)
    _ _ _ _ _ _ _);
  [ psb_sbm | first [reflexivity | assumption] | psb_free_reg HS E | psb_free_reg HS E | psb_free_reg HS E | psb_free_reg HS E
  | psb_free_reg HS E | ] end.

(* ---- a0 = -1 after a hex4 (460 or 972): the bnez to PSB_FREE ---- *)
Lemma psb_runN : forall CTX CW (D : ps_in) ly S Hp W regs mem md out w r Q pc s5o,
  psb_seg_freeP B ARx SK CTX CW P -> ps_pre CTX CW D -> psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 10 = w64 (-1) -> getr regs 21 = w64 (r + s5o) -> (pc = 460 \/ pc = 972) ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None ->
  SRr segs W (cfg_at segs (psb_pc pc) regs mem md) (ps_post CW D).
Proof.
intros CTX CW D ly S Hp W regs mem md out w r Q pc s5o FREE HPRE HI H10 H21 Hpc Hdec.
pose proof (psb_stN CTX CW D ly S Hp W regs mem md out w r Q pc (-1) s5o HPRE HI H10 H21) as HS.
pose proof HI as ((k & HC) & _ & _ & (H3 & H4) & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & H18 & _ & _ & H8 & _).
pose proof HC as (HJ & _).
pose proof (psb_env_img D regs []) as HEI.
assert (SHOK : sh_ok segs PSB_Bx [] (psb_E D regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + pc) with (BASE + (PSB_OFF + pc)) by lia.
destruct Hpc as [-> | ->].
- paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs []). exact Hdec.
- paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs []). exact Hdec.
Qed.


(* the window [sp + 36, sp + 40) a run's frame_of leaves free, as psb_inv_store reads it *)
Lemma psb_frame_win : forall (D : ps_in) regs X rs (m m' : word -> option byte),
  frame_of (psb_E D regs X) rs m m' ->
  (forall a, in_wrange (psb_E D regs X) rs a -> PS_SP D + 36 <= a < PS_SP D + 40) ->
  forall x : word, ~ (PS_SP D + 36 <= bv_unsigned x < PS_SP D + 40) -> m' x = m x.
Proof. intros D regs X rs m m' HF Hw x Hx. apply HF. intros Hin. exact (Hx (Hw _ Hin)). Qed.
Ltac psb_win_tac := let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (rg & Hin & Ha); cbn [ss_mem add_cond In] in Hin;
  repeat (destruct Hin as [<-|Hin];
    [cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi psb_rg_frame psb_rg_qe psb_rg_sh8 psb_rg_t67] in Ha;
     first [lia | (rewrite (psb_ew_lo _ _ _ 2 2 eq_refl) in Ha; unfold PS_Gen.PS_SP; rewrite psb_frame; unfold spZ; lia)]|]);
  destruct Hin.

(* ---- STRETCH C (972, after the second hex4): the low half's test, the pair, its store at sp + 36, put_utf8 ---- *)
Lemma psb_runC : forall CTX CW m (D : ps_in) ly S Hp W regs mem md out w r Q h,
  psb_seg_freeP B ARx SK CTX CW P -> psb_dec_ltP B ARx SK CTX CW P m -> ps_pre CTX CW D ->
  psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 21 = w64 (r + 6) ->
  val_mem segs (rdW W mem) (PS_SP D + 36) 4 h ->
  PjGrammar.hex4 (firstn 4 (rest_atR (pi_tb D) (pi_text D) (r + 2))) = Some h ->
  55296 <= h < 56320 -> r + 12 <= pi_text D + pi_len D ->
  nth_error (pi_tb D) (Z.to_nat (r + 6 - pi_text D)) = Some 92 ->
  nth_error (pi_tb D) (Z.to_nat (r + 7 - pi_text D)) = Some 117 ->
  match PjGrammar.hex4 (firstn 4 (rest_atR (pi_tb D) (pi_text D) (r + 8))) with
  | Some lo => getr regs 10 = w64 0 /\ val_mem segs (rdW W mem) (PS_SP D + 32) 4 lo
  | None => getr regs 10 = w64 (-1)
  end ->
  (Q - Z.to_nat (r - (pi_p D + 1)) <= m)%nat ->
  SRr segs W (cfg_at segs (psb_pc 972) regs mem md) (ps_post CW D).
Proof.
intros CTX CW m D ly S Hp W regs mem md out w r Q h FREE HLT HPRE HI H21 Hh Hhx Hh0 Hl12 Hb6 Hb7 Hlo Hm.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof HI as ((k & HC) & HAL & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & HRO & HSC &
  Hsp & H18 & H19 & H20 & H8 & H9 & Hb0 & Hb1 & HDR).
pose proof HC as (HJ & _ & _ & _ & _ & HPM).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HE0 & _) & _).
assert (Hrt : pi_text D <= r) by lia.
destruct (PjGrammar.hex4 (firstn 4 (rest_atR (pi_tb D) (pi_text D) (r + 8)))) as [lo|] eqn:Elo.
2:{ apply (psb_runN CTX CW D ly S Hp W regs mem md out w r Q 972 6 FREE HPRE HI Hlo H21 ltac:(right; reflexivity)).
    apply (psu_dec_lo_none _ _ r h Hrt Hb0 Hb1 ltac:(lia) Hhx Hh0).
    rewrite (psu_low_at (pi_tb D) (pi_text D) (r + 6) ltac:(lia) Hb6 ltac:(replace (r + 6 + 1 - pi_text D) with (r + 7 - pi_text D) by lia; exact Hb7)).
    replace (r + 6 + 2) with (r + 8) by lia. rewrite Elo. reflexivity. }
destruct Hlo as (H10 & Hlov).
pose proof (psu_hex4_firstn (rest_atR (pi_tb D) (pi_text D) (r + 8))) as E8. rewrite Elo in E8.
destruct (psu_rest_split4 (pi_tb D) (pi_text D) (r + 8) ltac:(lia) ltac:(lia)) as (e0 & e1 & e2 & e3 & Er8).
rewrite Er8 in E8. symmetry in E8. pose proof (psu_hex4_some _ _ _ _ _ _ E8) as (Hlo0 & _).
pose proof (psb_stC CTX CW D ly S Hp W regs mem md out w r Q h lo HPRE HI H10 H21 Hh Hh0 Hlov Hlo0) as HS.
pose proof (psb_env_img D regs (psb_XC D h lo)) as HEI.
assert (SHOK : sh_ok segs PSB_Bx [] (psb_E D regs (psb_XC D h lo)) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (U65 : U (psb_E D regs (psb_XC D h lo)) (SOff 65 0) = h) by (apply U_atom; [unfold psb_XC; psb_ew; reflexivity | lia]).
assert (U66 : U (psb_E D regs (psb_XC D h lo)) (SOff 66 0) = lo) by (apply U_atom; [unfold psb_XC; psb_ew; reflexivity | lia]).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + 972) with (BASE + (PSB_OFF + 972)) by lia.
psb_run_w RUNI HS HJ SHOK HPM PSB_Bspan; [psb_wr_fr HE0|].
assert (FW1 : forall x : word, ~ (PS_SP D + 36 <= bv_unsigned x < PS_SP D + 40) -> rdW W (ms_mem ms) x = rdW W mem x)
  by (apply (psb_frame_win D regs (psb_XC D h lo) _ _ _ HFr); psb_win_tac).
destruct (psb_inv_store CTX CW D ly S Hp W regs mem md out w r Q k (ms_mem ms) _ HPRE HI HC HJ ltac:(psb_sbm) FW1 HPM) as [HI1 HC1].
clear HF HG HFr FW1.
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite (psu_U_off _ 66 (-57344) lo) in Hc by (first [unfold psb_XC; psb_ew; reflexivity | lia]).
  rewrite U_SLit in Hc. change (zcanon 18446744073709550592) with 18446744073709550592 in Hc.
  pose proof (psu_low_test2 lo Hlo0) as LT. rewrite (proj2 (Z.ltb_lt _ _) Hc) in LT.
  psb_run_to_w RUNTOI HS HJ SHOK HPM PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_fr HE0|].
  assert (FW2 : forall x : word, ~ (PS_SP D + 36 <= bv_unsigned x < PS_SP D + 40) -> rdW W (ms_mem ms0) x = rdW W (ms_mem ms) x)
    by (apply (psb_frame_win D regs (psb_XC D h lo) _ _ _ HFr); psb_win_tac).
  destruct (psb_inv_store CTX CW D ly S Hp W regs (ms_mem ms) _ out w r Q k (ms_mem ms0) _ HPRE HI1 HC1 HJ ltac:(psb_sbm) FW2 HPM) as [HI2 HC2].
  psb_free_tac FREE HPRE HI2 HC2 HJ HS (psb_E D regs (psb_XC D h lo)).
  rewrite (psu_dec_pair _ _ r h lo Hrt Hb0 Hb1 ltac:(lia) Hhx Hh0 Hb6 Hb7 Elo).
  destruct ((56320 <=? lo) && (lo <=? 57343)); [discriminate | reflexivity]. }
psb_run_w RUNI HS HJ SHOK HPM PSB_Bspan; [psb_wr_fr HE0|].
assert (FW2 : forall x : word, ~ (PS_SP D + 36 <= bv_unsigned x < PS_SP D + 40) -> rdW W (ms_mem ms0) x = rdW W (ms_mem ms) x)
  by (apply (psb_frame_win D regs (psb_XC D h lo) _ _ _ HFr); psb_win_tac).
destruct (psb_inv_store CTX CW D ly S Hp W regs (ms_mem ms) _ out w r Q k (ms_mem ms0) _ HPRE HI1 HC1 HJ ltac:(psb_sbm) FW2 HPM) as [HI2 HC2].
clear HF HG HFr FW2.
rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
rewrite (psu_U_off _ 66 (-57344) lo) in Hc by (first [unfold psb_XC; psb_ew; reflexivity | lia]).
rewrite U_SLit in Hc. change (zcanon 18446744073709550592) with 18446744073709550592 in Hc.
pose proof (psu_low_test2 lo Hlo0) as LT. rewrite (proj2 (Z.ltb_ge _ _) Hc) in LT.
assert (Hlor : 56320 <= lo <= 57343) by (destruct (Z.leb_spec 56320 lo), (Z.leb_spec lo 57343); cbn in LT; try discriminate; lia).
rewrite wvb_collapse in HJ, HI2, HC2.
pose proof (psu_utf8_len (PjGrammar.pair_cp h lo) ltac:(unfold PjGrammar.pair_cp; lia)) as Hlen.
pose proof HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDR2).
pose proof HDR2 as (done2 & _ & _ & _ & _ & Hr2 & Hw2 & Hwr2 & Hsc2).
pose proof (psu_scan_pair _ _ r h lo Hrt Hb0 Hb1 ltac:(lia) Hhx Hb6 Hb7 Elo) as Hscan.
assert (Hr12 : r + 12 <= pi_p D + 1 + Z.of_nat Q).
{ rewrite Hsc2 in Hscan. destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 12))) as [q12|]; [|discriminate].
  cbn [option_map] in Hscan. injection Hscan as Hscan. lia. }
lazymatch goal with HS : st_ok _ ?E ?ss _ |- _ =>
refine (psb_put_call CTX CW D ly S Hp W regs (ms_mem ms0) _ out w r Q k E ss ms0 _ (PjGrammar.pair_cp h lo) 1044 HPRE HI2 HC2 HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl (same_but_materialized_refl _) HJ _ _ _ _ _ _ _ _ _) end.
- psb_crs HS (psb_E D regs (psb_XC D h lo)).
{ pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
  pose proof HWIN as (He0' & _ & Hetop & _).
  pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
  rewrite H8, H9. unfold w64. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
- psb_cpost HS (psb_E D regs (psb_XC D h lo)) (10%bv : bv 5) Hx. rewrite Hx. cbn [sv_denot]. psb_ew.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H19.
- psb_cpost HS (psb_E D regs (psb_XC D h lo)) (11%bv : bv 5) Hx. rewrite Hx. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite psu_U_pair, U65, U66. unfold PjGrammar.pair_cp.
  replace (h * 1024 - 56613888 + lo) with (65536 + (h - 55296) * 1024 + (lo - 56320)) by lia. apply Z.mod_small. lia.
- psb_cpost HS (psb_E D regs (psb_XC D h lo)) (1%bv : bv 5) Hx. prreg_norm Hx. rewrite Hx. unfold w64. f_equal.
- unfold PjGrammar.pair_cp. lia.
- lia.
- vm_compute. split; congruence.
- vm_compute. reflexivity.
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 HI3 H21' H10' HBY.
  pose proof HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDR3).
  assert (Hdeq : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) =
    PjGrammar.emit (PjGrammar.utf8 (PjGrammar.pair_cp h lo)) (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) (r + 12)))).
  { rewrite (psu_dec_pair _ _ r h lo Hrt Hb0 Hb1 ltac:(lia) Hhx Hh0 Hb6 Hb7 Elo).
    replace ((56320 <=? lo) && (lo <=? 57343)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    reflexivity. }
  pose proof (psb_dec_rel_step D W2 mem2 out w r Q (r + 12) (PjGrammar.pair_cp h lo) HDR3 HBY Hdeq Hscan ltac:(lia)) as HDR'.
  psb_cpost HS (psb_E D regs (psb_XC D h lo)) (21%bv : bv 5) Hx21. rewrite Hx21 in H21'. cbn [sv_denot] in H21'. rewrite (psb_ew_hi D regs (psb_XC D h lo) 52) in H21' by (unfold A_TEXT; lia).
cbn [Nat.sub nth psb_cur map all_regs app] in H21'. rewrite H20 in H21'. unfold w64 in H21'.
rewrite unsigned_lit_small in H21' by lia.
apply (psb_runD CTX CW m D ly2 S2 Hp2 W2 regs2 mem2 md2 out w r Q (r + 12) _ HLT HPRE HI3 HDR' H10' ltac:(lia) H21' ltac:(lia) Hm).
Qed.


(* ---- STRETCH B (460, after the first hex4): a0, h = 0, the surrogate tests, the second \u's two bytes, hex4 at r + 8
   (or the BMP path to put_utf8) ---- *)
Lemma psb_runB : forall CTX CW m (D : ps_in) ly S Hp W regs mem md out w r Q,
  psb_seg_freeP B ARx SK CTX CW P -> psb_dec_ltP B ARx SK CTX CW P m -> ps_pre CTX CW D ->
  psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 21 = w64 (r + 2) -> r + 6 <= pi_text D + pi_len D ->
  match PjGrammar.hex4 (firstn 4 (rest_atR (pi_tb D) (pi_text D) (r + 2))) with
  | Some h => getr regs 10 = w64 0 /\ val_mem segs (rdW W mem) (PS_SP D + 36) 4 h
  | None => getr regs 10 = w64 (-1)
  end ->
  (Q - Z.to_nat (r - (pi_p D + 1)) <= m)%nat ->
  SRr segs W (cfg_at segs (psb_pc 460) regs mem md) (ps_post CW D).
Proof.
intros CTX CW m D ly S Hp W regs mem md out w r Q FREE HLT HPRE HI H21 Hl6 Hhx4 Hm.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof HI as ((k & HC) & HAL & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & HRO & HSC &
  Hsp & H18 & H19 & H20 & H8 & H9 & Hb0 & Hb1 & HDR).
pose proof HC as (HJ & _).
assert (Hrt : pi_text D <= r) by lia.
destruct (PjGrammar.hex4 (firstn 4 (rest_atR (pi_tb D) (pi_text D) (r + 2)))) as [h|] eqn:Eh.
2:{ apply (psb_runN CTX CW D ly S Hp W regs mem md out w r Q 460 2 FREE HPRE HI Hhx4 H21 ltac:(left; reflexivity)).
    rewrite (psu_dec_u _ _ r Hrt Hb0 Hb1 ltac:(lia)), Eh. reflexivity. }
destruct Hhx4 as (H10 & Hhv).
pose proof (psu_hex4_firstn (rest_atR (pi_tb D) (pi_text D) (r + 2))) as E2. rewrite Eh in E2.
destruct (psu_rest_split4 (pi_tb D) (pi_text D) (r + 2) ltac:(lia) ltac:(lia)) as (e0 & e1 & e2 & e3 & Er2).
rewrite Er2 in E2. symmetry in E2. pose proof (psu_hex4_some _ _ _ _ _ _ E2) as (Hh0 & _).
pose proof (psb_stB CTX CW D ly S Hp W regs mem md out w r Q h HPRE HI H10 H21 Hhv Hh0) as HS.
pose proof (psb_env_img D regs (psb_XB D r h)) as HEI.
assert (SHOK : sh_ok segs PSB_Bx [] (psb_E D regs (psb_XB D r h)) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (U65 : U (psb_E D regs (psb_XB D r h)) (SOff 65 0) = h) by (apply U_atom; [unfold psb_XB; psb_ew; reflexivity | lia]).
assert (U52 : U (psb_E D regs (psb_XB D r h)) (SOff 52 0) = r) by (apply U_atom; [psb_ew; exact H20 | lia]).
assert (U64 : U (psb_E D regs (psb_XB D r h)) (SOff 64 0) = pi_text D + pi_len D)
  by (apply U_atom; [unfold psb_XB; psb_ew; reflexivity | lia]).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + 460) with (BASE + (PSB_OFF + 460)) by lia.
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U65, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs (psb_XB D r h)).
  rewrite (psu_dec_u _ _ r Hrt Hb0 Hb1 ltac:(lia)), Eh, Hc. reflexivity. }
assert (Hhn0 : h <> 0) by (intros ->; rewrite branch_eq_U, U65, U_SLit in Hc; change (zcanon 0) with 0 in Hc; rewrite Z.eqb_refl in Hc; discriminate).
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ rewrite branch_eq_U, psu_U_and1024, U65, U_SLit in Hc0. change (zcanon 55296) with 55296 in Hc0.
  rewrite psu_hi_test in Hc0 by lia.
  assert (Hhs : 55296 <= h < 56320) by (apply andb_prop in Hc0 as [Ha Hb']; apply Z.leb_le in Ha; apply Z.ltb_lt in Hb'; lia).
  paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
assert (U6 : U (psb_E D regs (psb_XB D r h)) (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 52 0) (SLit (-1))) (SLit (-6))) (SOff 64 0)) = pi_text D + pi_len D - r - 6).
{ rewrite psu_U_sub_c, U64, U52. apply Z.mod_small. lia. }
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ cbn [branch_taken] in Hc1. unfold bv_lts in Hc1. change (bv_signed (sv_denot ?E ?e)) with (Sg E e) in Hc1. rewrite !S_of_U in Hc1.
  rewrite U6, U_SLit in Hc1. change (zcanon 6) with 6 in Hc1.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hc1. cbn [Z.of_N] in Hc1.
  change (2 ^ 64 / 2) with (2 ^ 63) in Hc1. rewrite !Z.mod_small in Hc1 by lia. apply Z.ltb_lt in Hc1.
  paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs (psb_XB D r h)).
  rewrite (psu_dec_hi _ _ r h Hrt Hb0 Hb1 ltac:(lia) Eh Hhs).
  replace (r + 12 <=? pi_text D + Z.of_nat (length (pi_tb D))) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
cbn [branch_taken] in Hc1. unfold bv_lts in Hc1. change (bv_signed (sv_denot ?E ?e)) with (Sg E e) in Hc1. rewrite !S_of_U in Hc1.
rewrite U6, U_SLit in Hc1. change (zcanon 6) with 6 in Hc1.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hc1. cbn [Z.of_N] in Hc1.
change (2 ^ 64 / 2) with (2 ^ 63) in Hc1. rewrite !Z.mod_small in Hc1 by lia. apply Z.ltb_ge in Hc1.
assert (Hl12 : r + 12 <= pi_text D + pi_len D) by lia.
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan.
{ rewrite <- aview_rd_of, EM. unfold PSB_Bx. rewrite U_SLit, (psu_U_off _ 52 6 r) by (first [psb_ew; exact H20 | lia]).
  change (zcanon SHADOW_OFF) with SHADOW_OFF.
  pose proof HC as (_ & _ & _ & (_ & _ & _ & _ & HRA & _) & _).
  rewrite Z.mod_small by lia. rewrite R9 in HRA.
  apply (range_addressable_sub _ SHADOW_OFF (pi_text D) (pi_len D)); [exact HRA | lia | lia]. }
{ psb_wr_ro. }
psb_mem.
pose proof HPJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HTB & _).
assert (V6 : val_mem segs (rdW W mem) (r + 6) 1 (nth (Z.to_nat (r + 6 - pi_text D)) (pi_tb D) 0) /\
  0 <= nth (Z.to_nat (r + 6 - pi_text D)) (pi_tb D) 0 < 256).
{ destruct (HTB (Z.to_nat (r + 6 - pi_text D)) ltac:(lia)) as [Hv Hr'].
  replace (pi_text D + Z.of_nat (Z.to_nat (r + 6 - pi_text D))) with (r + 6) in Hv by lia. split; assumption. }
assert (V7 : val_mem segs (rdW W mem) (r + 7) 1 (nth (Z.to_nat (r + 7 - pi_text D)) (pi_tb D) 0) /\
  0 <= nth (Z.to_nat (r + 7 - pi_text D)) (pi_tb D) 0 < 256).
{ destruct (HTB (Z.to_nat (r + 7 - pi_text D)) ltac:(lia)) as [Hv Hr'].
  replace (pi_text D + Z.of_nat (Z.to_nat (r + 7 - pi_text D))) with (r + 7) in Hv by lia. split; assumption. }
apply (st_ok_pi_add_region _ _ _ psb_rg_t67) in HS; [| vm_compute; reflexivity | | ].
2:{ cbn [ms_mem restrict]. rewrite EM. unfold region_ok. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks psb_rg_t67].
rewrite !ew_ewset_other by lia. psb_ew. rewrite H20. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val _ _ _ _ 6 1 (SOff 66 0) (nth (Z.to_nat (r + 6 - pi_text D)) (pi_tb D) 0)).
  + cbn [sv_denot]. rewrite !ew_ewset_other by lia. unfold psb_XB. psb_ew. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + cbn. lia.
  + cbn. lia.
  + exact (proj1 V6).
- apply (chunk_ok_val _ _ _ _ 7 1 (SOff 67 0) (nth (Z.to_nat (r + 7 - pi_text D)) (pi_tb D) 0)).
  + cbn [sv_denot]. rewrite !ew_ewset_other by lia. unfold psb_XB. psb_ew. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + cbn. lia.
  + cbn. lia.
  + exact (proj1 V7). }
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi psb_rg_t67 psb_rg_frame psb_rg_qe psb_rg_sh8]. rewrite !ew_ewset_other by lia. psb_ew.
pose proof HC as (_ & _ & _ & (_ & _ & _ & Hamr & _) & _). rewrite R9 in Hamr. unfold amem_range in Hamr.
pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
pose proof HWIN as (He0' & _ & Hetop & _).
pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
pose proof asan_consts as (C1 & _).
assert (Hdq : 0 <= (pi_q D + 8) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold spZ in *; lia).
rewrite H20, H8, H24. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, spZ in *; lia).
unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, spZ in *. pose proof psb_stk_callees as (K0 & K1 & _).
repeat split; try exact I; lia. }
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
set (t6 := nth (Z.to_nat (r + 6 - pi_text D)) (pi_tb D) 0) in *.
set (t7 := nth (Z.to_nat (r + 7 - pi_text D)) (pi_tb D) 0) in *.
assert (N6 : nth_error (pi_tb D) (Z.to_nat (r + 6 - pi_text D)) = Some t6) by (apply nth_error_nth'; lia).
assert (N7 : nth_error (pi_tb D) (Z.to_nat (r + 7 - pi_text D)) = Some t7) by (apply nth_error_nth'; lia).
assert (U66 : U (ewset (ewset (psb_E D regs (psb_XB D r h)) 512 w0) 513 w1) (SExt false 8 (SOff 66 0)) = t6).
{ rewrite U_SExt. rewrite (U_atom _ 66 t6) by (first [rewrite !ew_ewset_other by lia; unfold psb_XB; psb_ew; reflexivity | lia]).
  change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small t6) by lia. unfold zcanon, M64. apply Z.mod_small. lia. }
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ rewrite branch_ne_U, U66, U_SLit in Hc2. change (zcanon 92) with 92 in Hc2.
  apply negb_true_iff, Z.eqb_neq in Hc2.
  paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs (psb_XB D r h)).
  apply (psu_dec_lo_none _ _ r h Hrt Hb0 Hb1 ltac:(lia) Eh Hhs).
  apply (psu_low_b0 (pi_tb D) (pi_text D) (r + 6) t6 ltac:(lia) ltac:(lia) N6 Hc2). }
rewrite branch_ne_U, U66, U_SLit in Hc2. change (zcanon 92) with 92 in Hc2.
apply negb_false_iff, Z.eqb_eq in Hc2.
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan.
{ rewrite <- aview_rd_of, EM. unfold PSB_Bx. rewrite U_SLit, (psu_U_off _ 52 7 r) by (first [rewrite !ew_ewset_other by lia; psb_ew; exact H20 | lia]).
  change (zcanon SHADOW_OFF) with SHADOW_OFF.
  pose proof HC as (_ & _ & _ & (_ & _ & _ & _ & HRA & _) & _).
  rewrite Z.mod_small by lia. rewrite R9 in HRA.
  apply (range_addressable_sub _ SHADOW_OFF (pi_text D) (pi_len D)); [exact HRA | lia | lia]. }
{ psb_wr_ro. }
psb_mem.
lazymatch goal with HS : st_ok_pi _ _ ?E _ _ |- _ =>
  assert (U67 : U E (SExt false 8 (SOff 67 0)) = t7) end.
{ rewrite U_SExt. rewrite (U_atom _ 67 t7) by (first [rewrite !ew_ewset_other by lia; unfold psb_XB; psb_ew; reflexivity | lia]).
  change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small t7) by lia. unfold zcanon, M64. apply Z.mod_small. lia. }
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ rewrite branch_ne_U, U67, U_SLit in Hc3. change (zcanon 117) with 117 in Hc3.
  apply negb_true_iff, Z.eqb_neq in Hc3.
  paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs (psb_XB D r h)).
  apply (psu_dec_lo_none _ _ r h Hrt Hb0 Hb1 ltac:(lia) Eh Hhs).
  apply (psu_low_b1 (pi_tb D) (pi_text D) (r + 6) t7 ltac:(lia) ltac:(lia)
    ltac:(replace (r + 6 + 1 - pi_text D) with (r + 7 - pi_text D) by lia; exact N7) Hc3). }
rewrite branch_ne_U, U67, U_SLit in Hc3. change (zcanon 117) with 117 in Hc3.
apply negb_false_iff, Z.eqb_eq in Hc3.
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|].
psb_mem. rewrite EM in HJ.
repeat rewrite wvb_collapse in HJ.
lazymatch goal with HS : st_ok _ ?E ?ss _ |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
refine (psb_hex4_call CTX CW D ly S Hp W regs mem md out w r Q k E ss ms mdx 8 32 972 HPRE HI HC HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) EM ltac:(psb_sbm) HJ _ _ _ _ ltac:(lia) ltac:(lia)
  ltac:(left; reflexivity) ltac:(vm_compute; split; congruence) ltac:(vm_compute; reflexivity) _) end.
- psb_crs HS (psb_E D regs (psb_XB D r h)).
  { pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
    pose proof HWIN as (He0' & _ & Hetop & _).
    pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
    rewrite H8, H9. unfold w64. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
- psb_cpost HS (psb_E D regs (psb_XB D r h)) (10%bv : bv 5) Hx. rewrite Hx. cbn [sv_denot]. psb_ew.
  rewrite H20. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- psb_cpost HS (psb_E D regs (psb_XB D r h)) (11%bv : bv 5) Hx. rewrite Hx. cbn [sv_denot]. psb_ew.
  unfold w64, PS_Gen.PS_SP, spZ. rewrite psb_frame. f_equal. lia.
- psb_cpost HS (psb_E D regs (psb_XB D r h)) (1%bv : bv 5) Hx. prreg_norm Hx. rewrite Hx. unfold w64. f_equal.
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 HI3 H21' HK3 Hlo3.
  psb_cpost HS (psb_E D regs (psb_XB D r h)) (21%bv : bv 5) Hx21. rewrite Hx21 in H21'. cbn [sv_denot] in H21'.
  rewrite (psb_ew_hi D regs (psb_XB D r h) 52) in H21' by (unfold A_TEXT; lia).
  cbn [Nat.sub nth psb_cur map all_regs app] in H21'. rewrite H20 in H21'. unfold w64 in H21'.
  rewrite unsigned_lit_small in H21' by lia.
  assert (Hh3 : val_mem segs (rdW W2 mem2) (PS_SP D + 36) 4 h).
  { refine (psb_val_mem_keep W W2 mem mem2 (PS_SP D + 36) 4 h _ Hhv). intros i Hi. apply HK3;
      unfold PS_Gen.PS_SP, spZ in *; rewrite psb_frame in *; lia. }
  rewrite Hc2 in N6. rewrite Hc3 in N7.
  exact (psb_runC CTX CW m D ly2 S2 Hp2 W2 regs2 mem2 md2 out w r Q h FREE HLT HPRE HI3 H21' Hh3 Eh Hhs Hl12 N6 N7 Hlo3 Hm).
}
rewrite branch_eq_U, psu_U_and1024, U65, U_SLit in Hc0. change (zcanon 55296) with 55296 in Hc0.
rewrite psu_hi_test in Hc0 by lia.
assert (Hhs' : ~ (55296 <= h < 56320)) by (intros [Ha Hb']; apply Z.leb_le in Ha; apply Z.ltb_lt in Hb'; rewrite Ha, Hb' in Hc0; discriminate).
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ rewrite branch_eq_U, psu_U_and1024, U65, U_SLit in Hc1. change (zcanon 56320) with 56320 in Hc1.
  rewrite psu_lo_test in Hc1 by lia.
  assert (Hlw : 56320 <= h < 57344) by (apply andb_prop in Hc1 as [Ha Hb']; apply Z.leb_le in Ha; apply Z.ltb_lt in Hb'; lia).
  paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs (psb_XB D r h)).
  rewrite (psu_dec_u _ _ r Hrt Hb0 Hb1 ltac:(lia)), Eh.
  replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((55296 <=? h) && (h <? 56320)) with false
    by (symmetry; destruct (Z.leb_spec 55296 h), (Z.ltb_spec h 56320); cbn; [lia | reflexivity ..]).
  replace ((56320 <=? h) && (h <? 57344)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity. }
rewrite branch_eq_U, psu_U_and1024, U65, U_SLit in Hc1. change (zcanon 56320) with 56320 in Hc1.
rewrite psu_lo_test in Hc1 by lia.
assert (Hlw' : ~ (56320 <= h < 57344)) by (intros [Ha Hb']; apply Z.leb_le in Ha; apply Z.ltb_lt in Hb'; rewrite Ha, Hb' in Hc1; discriminate).
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem. rewrite EM in HJ. repeat rewrite wvb_collapse in HJ.
pose proof (psu_utf8_len h ltac:(lia)) as Hlen.
pose proof (psu_scan6 _ _ r h Hrt Hb0 Hb1 ltac:(lia) Eh) as Hscan.
pose proof HDR as (done2 & _ & _ & _ & _ & Hr2 & Hw2 & Hwr2 & Hsc2).
assert (Hr6 : r + 6 <= pi_p D + 1 + Z.of_nat Q).
{ rewrite Hsc2 in Hscan. destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 6))) as [q6|]; [|discriminate].
  cbn [option_map] in Hscan. injection Hscan as Hscan. lia. }
lazymatch goal with HS : st_ok _ ?E ?ss _ |- SRr _ _ {| cfg_ms := ?ms; cfg_model := ?mdx |} _ =>
refine (psb_put_call CTX CW D ly S Hp W regs mem md out w r Q k E ss ms mdx h 1044 HPRE HI HC HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) EM ltac:(psb_sbm) HJ _ _ _ _ ltac:(lia) ltac:(lia)
  ltac:(vm_compute; split; congruence) ltac:(vm_compute; reflexivity) _) end.
- psb_crs HS (psb_E D regs (psb_XB D r h)).
  { pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
    pose proof HWIN as (He0' & _ & Hetop & _).
    pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
    rewrite H8, H9. unfold w64. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
- psb_cpost HS (psb_E D regs (psb_XB D r h)) (10%bv : bv 5) Hx. rewrite Hx. cbn [sv_denot]. psb_ew.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H19.
- psb_cpost HS (psb_E D regs (psb_XB D r h)) (11%bv : bv 5) Hx. rewrite Hx. cbn [sv_denot].
  unfold psb_XB. psb_ew. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- psb_cpost HS (psb_E D regs (psb_XB D r h)) (1%bv : bv 5) Hx. prreg_norm Hx. rewrite Hx. unfold w64. f_equal.
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 HI3 H21' H10' HBY.
  pose proof HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDR3).
  pose proof (psu_dec_bmp _ _ r h Hrt Hb0 Hb1 ltac:(lia) Eh Hhn0 Hhs' Hlw') as Hdeq.
  pose proof (psb_dec_rel_step D W2 mem2 out w r Q (r + 6) h HDR3 HBY Hdeq
    ltac:(rewrite (psu_scan6 _ _ r h Hrt Hb0 Hb1 ltac:(lia) Eh); reflexivity) ltac:(lia)) as HDR'.
  psb_cpost HS (psb_E D regs (psb_XB D r h)) (21%bv : bv 5) Hx21. rewrite Hx21 in H21'. cbn [sv_denot] in H21'.
  rewrite (psb_ew_hi D regs (psb_XB D r h) 52) in H21' by (unfold A_TEXT; lia).
  cbn [Nat.sub nth psb_cur map all_regs app] in H21'. rewrite H20 in H21'. unfold w64 in H21'.
  rewrite unsigned_lit_small in H21' by lia.
  apply (psb_runD CTX CW m D ly2 S2 Hp2 W2 regs2 mem2 md2 out w r Q (r + 6) _ HLT HPRE HI3 HDR' H10' ltac:(lia) H21' ltac:(lia) Hm).
Qed.

(* ---- STRETCH A (PSB_U = 436): the four-digit length test, then `jal hex4` at 456 with a0 = r + 2, a1 = sp + 36 ---- *)
Lemma psb_runA : forall CTX CW m (D : ps_in) ly S Hp W regs mem md out w r Q,
  psb_seg_freeP B ARx SK CTX CW P -> psb_dec_ltP B ARx SK CTX CW P m -> ps_pre CTX CW D ->
  psb_inv D ly S Hp W regs mem md out w r Q ->
  getr regs 10 = w64 (pi_text D + pi_len D) -> getr regs 21 = w64 (r + 2) ->
  (Q - Z.to_nat (r - (pi_p D + 1)) <= m)%nat ->
  SRr segs W (cfg_at segs (psb_pc PSB_U) regs mem md) (ps_post CW D).
Proof.
intros CTX CW m D ly S Hp W regs mem md out w r Q FREE HLT HPRE HI H10 H21 Hm.
pose proof (psb_ranges CTX CW D ly S Hp W regs mem md out w r Q HPRE HI) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
pose proof HI as ((k & HC) & HAL & (H23 & H22 & H24) & (H3 & H4) & H25 & H26 & H27 & V24 & V16 & V8 & HPJ & HRO & HSC &
  Hsp & H18 & H19 & H20 & H8 & H9 & Hb0 & Hb1 & HDR).
pose proof HC as (HJ & _).
assert (Hrt : pi_text D <= r) by lia.
pose proof (psb_stA CTX CW D ly S Hp W regs mem md out w r Q HPRE HI H10 H21) as HS.
pose proof (psb_env_img D regs []) as HEI.
assert (SHOK : sh_ok segs PSB_Bx [] (psb_E D regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (U42 : U (psb_E D regs []) (SOff 42 (-2)) = pi_text D + pi_len D - 2)
  by (rewrite (psu_U_off _ 42 (-2) (pi_text D + pi_len D)) by (first [psb_ew; exact H10 | lia]); apply Z.mod_small; lia).
assert (U52 : U (psb_E D regs []) (SOff 52 0) = r) by (apply U_atom; [psb_ew; exact H20 | lia]).
assert (UA : U (psb_E D regs []) (SAlu ALU_ADD (SOff 42 (-2)) (SMd M_MUL (SOff 52 0) (SLit (-1)))) = pi_text D + pi_len D - (r + 2))
  by (rewrite psu_U_sub, U42, U52; replace (pi_text D + pi_len D - 2 - r) with (pi_text D + pi_len D - (r + 2)) by lia; apply Z.mod_small; lia).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + PSB_U) with (BASE + (PSB_OFF + PSB_U)) by lia.
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem.
psrr_branch_tok RUN BR HS SHOK PSB_Bspan.
1:{ cbn [branch_taken] in Hc. unfold bv_lts in Hc. change (bv_signed (sv_denot ?E ?e)) with (Sg E e) in Hc. rewrite !S_of_U in Hc.
  rewrite UA, U_SLit in Hc. change (zcanon 4) with 4 in Hc.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hc. cbn [Z.of_N] in Hc.
  change (2 ^ 64 / 2) with (2 ^ 63) in Hc. rewrite !Z.mod_small in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK PSB_Bspan (PSB_OFF + PSB_FREE); [psb_wr_ro|]. psb_mem. rewrite EM in HJ.
  psb_free_tac FREE HPRE HI HC HJ HS (psb_E D regs []).
  apply (psu_dec_short_at _ _ r Hrt Hb0 Hb1). lia. }
cbn [branch_taken] in Hc. unfold bv_lts in Hc. change (bv_signed (sv_denot ?E ?e)) with (Sg E e) in Hc. rewrite !S_of_U in Hc.
rewrite UA, U_SLit in Hc. change (zcanon 4) with 4 in Hc.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hc. cbn [Z.of_N] in Hc.
change (2 ^ 64 / 2) with (2 ^ 63) in Hc. rewrite !Z.mod_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_tok_x RUN HS HJ SHOK PSB_Bspan; [psb_wr_ro|]. psb_mem. rewrite EM in HJ. repeat rewrite wvb_collapse in HJ.
lazymatch goal with HS : st_ok _ ?E ?ss _ |- SRr _ _ {| cfg_ms := ?ms; cfg_model := ?mdx |} _ =>
refine (psb_hex4_call CTX CW D ly S Hp W regs mem md out w r Q k E ss ms mdx 2 36 460 HPRE HI HC HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) EM ltac:(psb_sbm) HJ _ _ _ _ ltac:(lia) ltac:(lia)
  ltac:(right; reflexivity) ltac:(vm_compute; split; congruence) ltac:(vm_compute; reflexivity) _) end.
- psb_crs HS (psb_E D regs []).
  { pose proof HPRE as (_ & _ & _ & _ & _ & Hqg & _ & _ & _ & _ & _ & _ & _ & HWIN & Hq0 & Hq24 & _).
    pose proof HWIN as (He0' & _ & Hetop & _).
    pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & Hstk0 & _ & Hslo & Hshi & H47 & _ & Htop1 & Htop2) & _) & _) & _).
    rewrite H8, H9. unfold w64. rewrite unsigned_lit_small by (unfold spZ in *; lia). reflexivity. }
- psb_cpost HS (psb_E D regs []) (10%bv : bv 5) Hx. rewrite Hx. cbn [sv_denot]. psb_ew.
  rewrite H20. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- psb_cpost HS (psb_E D regs []) (11%bv : bv 5) Hx. rewrite Hx. cbn [sv_denot]. psb_ew.
  unfold w64, PS_Gen.PS_SP, spZ. rewrite psb_frame. f_equal. lia.
- psb_cpost HS (psb_E D regs []) (1%bv : bv 5) Hx. prreg_norm Hx. rewrite Hx. unfold w64. f_equal.
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 HI3 H21' HK3 Hh3.
  psb_cpost HS (psb_E D regs []) (21%bv : bv 5) Hx21. rewrite Hx21 in H21'. cbn [sv_denot] in H21'.
  rewrite (psb_ew_hi D regs [] 52) in H21' by (unfold A_TEXT; lia).
  cbn [Nat.sub nth psb_cur map all_regs app] in H21'. rewrite H20 in H21'. unfold w64 in H21'.
  rewrite unsigned_lit_small in H21' by lia.
  exact (psb_runB CTX CW m D ly2 S2 Hp2 W2 regs2 mem2 md2 out w r Q FREE HLT HPRE HI3 H21' ltac:(lia) Hh3 Hm).
Qed.

End runs.
End pu.

(* ---- THE STRETCH AT A GENERIC INVARIANT P (the internal file GP-BRIEF.md): the old premise at psb_seg_freeP P, the conclusion
   psb_seg_uP P; srr_inv_laws and srr_inv_call (the stretch crosses the kit-text calls hex4 and put_utf8) ---- *)
Theorem psb_u_holdsP : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> srr_inv_call segs P ->
  psb_seg_freeP B ARx SK CTX CW P -> psb_seg_uP B ARx SK CTX CW P.
Proof.
intros CTX CW P PLAW PCALL FREE m HLT D ly S Hp W regs mem md out w r Q HPRE HU Hm.
destruct (psb_inv_of_at_u P D ly S Hp W regs mem md out w r Q HU) as (HI & H10 & H21).
apply ps_finP_SRr'.
exact (psb_runA P PLAW PCALL CTX CW m D ly S Hp W regs mem md out w r Q FREE HLT HPRE HI H10 H21 Hm).
Qed.

(* ---- THE OLD STATEMENT, unchanged, as the corollary at P := fun _ => True (PSB_Base's psb_seg_u_of_True /
   psb_seg_free_of_True, PS_Gen's srr_inv_laws_True / srr_inv_call_True); its statement did not move ---- *)
Theorem psb_u_holds : forall CTX CW, psb_seg_free B ARx SK CTX CW -> psb_seg_u B ARx SK CTX CW.
Proof.
intros CTX CW FREE. apply (proj1 (psb_seg_u_of_True B ARx SK CTX CW)).
exact (psb_u_holdsP CTX CW (fun _ => True) srr_inv_laws_True srr_inv_call_True
  (proj2 (psb_seg_free_of_True B ARx SK CTX CW) FREE)).
Qed.
End psu.
