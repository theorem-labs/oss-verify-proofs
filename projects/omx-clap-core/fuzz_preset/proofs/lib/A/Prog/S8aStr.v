(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumE.v, with its module paths and module names changed; 1015 of its 1127 lines of code are new or changed and 1803 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (#102 asan, 1be0f53d / unstripped twin bff8519b): PIECE 3 of the walk of
   ex_value (A 0x832a4), ev_string: 0x834cc-0x83550, 0x83cb0-0x83cb4 and the report arms 0x83e90-0x83ea0,
   0x83ebc-0x83ec8, 0x8400c-0x84014 (48 instructions), from P_KIND at EV_STR through `jal ex_string`, v->type and
   `jal wrapper_strcmp` to P_EXIT; and ev_disp (pieces 2 + 3 + 4, S8aIface's ev_disp_spec) from S8aDisp's d_ws.
   Walked: 0x834cc-0x834d0 to the call (ev_str_call), 0x834d4 a0 = -1 (ev_str_none), 0x834d4-0x834d8 + 0x83cb0-0x83cb4
   v = 0 (ev_str_v0), and the v <> 0 tail ev_str_vn: 0x834d4-0x83528 (v's 4-byte check, v->type, the 8-byte checks of
   v + 16 and q + 24, the loads of v->str and in->scratch), `jal wrapper_strcmp` by YGcallMx.aj_strcmp_at_x, then
   0x8352c / 0x83cb0-0x83cb4 (equal: in->differs kept) or 0x83530-0x83550 (type <> PJ_STRING or unequal: the 4-byte
   check of q + 32 and in->differs := 1). The report arms 0x83e90-0x83ea0, 0x83ebc-0x83ec8, 0x8400c-0x84014 are absorbed
   by the engine (YCbn tok_load), never visited: their shadow tests are discharged from prhex_tree's range_addressable
   (v, v + 16) and the real stack's zero shadow ZSB_x (q + 24, q + 32). ev_string = ev_string_of_vn ev_str_vn;
   ev_disp = ev_disp_of ev_string (S8aWord's ev_word).
   Base and conventions: as lib/A/Prog/S8aWord.v (#102: the S8a of record commit
   6d4ad7fbfc10, moved from b8ea5a686a5 by alreloc c4338d099cfb8025 plus hand fixes, docs/S8A102-RELOC-AUDIT.md;
   re-fit: ledger cells ea_most / ea_own, fpre's frm_zero at the ex_string call from ev_fx; the call kit ev_call_st /
   ev_rod / ev_chain / ev_mid_rt is S8aWord's; call rule YCbqGcallW's aj_call_xWF_d). Addresses: the call sites
   0x834d0 (-> ex_string 0x84034) and 0x83528 (-> wrapper_strcmp) are the listing's PCall slots, checked on the twin
   (S8aWord.v header).
   RE-PROVED (2026-10-29): the ev_string / ev_disp of commit 9d7dd411769 are WITHDRAWN
   (the unit owner): ev_string took HROM ("no in_rom byte is owned-static or errno"), FALSE at the instance (the owned
   statics (66280, 8) and (118364, 21) lie inside in_rom on the old-pin images A and B), and ev_disp took HROM
   through ev_string and the then-false WORDX through ev_word. HROM is DELETED: the strcmp call is the read-only rule
   YGcallMxmn.aj_strcmp_at_xrom at the row's xrom text (SCMP, stated as pieces 7 + 8 state it, S8aItemsTop.v at
   commit f2bdcc4ec76), whose read-only premise arodata_okP over the call's view is a
   fact of the walk's STATE: S8aWord.ev_rod at the call's memory (fpre's entry arodata_okP, kept by the journal's image
   clause). On #102 the kit and the engine read ONE arodata_okP (PresetRodata.v 4eb7e95e7e93; PRH_Base re-exports
   it, YGcallMxmn b47cf7942c3d Requires it), so the old copy conversion ev_aro_mxmn is gone. No premise about the
   image is added.
   HBLK32 is gone too: v->str's `kx + 1 < 2 ^ 32` is now the kit's pj_cstrR conjunct (PRH_Reader.v:113). MEMNORM: as
   S8aWord.v (the _inv runners; across ex_string the text's m-form keep, across strcmp the xrom rule's keep; ev_mid_av
   takes it at the new memory).
   SECTION HYPOTHESES: LAWS (AR_laws_x), STRX (tex_string_specX), SCMP (the strcmp row, xrom form), HSHD, HAM8 (each
   with its discharge route at its text), WORDX and TS (S8aWord.v's, for ev_word in ev_disp; LIT is deleted).
   The small byte / view helpers vn_byte_eq .. vn_str_eq, vn_br_eq_t / _f are COPIED from lane E's S8aNumE.v
   (da73e1570f8, not Required: it does not build on this base). ev_mid_av is S8aDisp's ev_mid_frame with a view premise.
   Every conclusion is srealizes through SRr. No released plain or UBSan file is Required, no lemma of one cited.
   NUMERALS (rule 7): EV_* offsets (LENGTH: pc - 0x832a4 on the bff8519b listing); 34 (WORD: the quote); 4 (WORD:
   PJ_STRING); 8, 16, 24, 32, 36, 40, 56 (LENGTH: word, struct ex / tree node fields); 0 / 1 (WORD: NULL, the differs
   flag); 6 (WORD: the largest tag); 8192 (DERIVED: 2 * ESTACK, strcmp's window); 2 ^ 32, 2 ^ 47, 2 ^ 64 (DERIVED: word /
   address bounds); the atom indices of the tail's symbolic state (19 s3, 23 s7, 24 s8, 10 a0, 2 sp; 32 in->scratch,
   33 in->differs, 34 v->type, 35 v->str; 48 the havoc base after the call and 52 its a0, CLOB's fifth entry); 7924
   (DERIVED: ex_string's return pc 0x834d4 - A_prog_base 0x815e0 on A', a listing position; 7188 on the old image).
   No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallMx YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aModel S8aDisp S8aWord.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation PIA := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation PL := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PIA)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the real stack's shadow bytes read 0 (S8aDisp's ZSB_x text = the engine's alx_zshadow_byte, AR_laws_x field 13) *)
Lemma ZSB_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
  aview SEGS (w_H W) mem (SHADOW_OFF + a / 8) = Some 0.
Proof. exact (alx_zshadow_byte SEGS B ARx LAWS). Qed.
(* STAND-IN: the cf layer's writer; S8aNumber.v's HSHD verbatim, as S8aWord.v's (same text, same reason). DISCHARGE at
   the preset instance: AR_shadow_law_ok_cf (YG0sshcf.v:160, a Theorem over ARcf). A law of ARx's states, no image fact. *)
Hypothesis HSHD : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  block_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (p + hd_skip Hp p) (req_size n - hd_skip Hp p) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) p (req_size n).
(* The fake-frame and real-stack hulls of a tree root (through S8aWord.ev_mid_rt) are S8aWord's ev_frame_hull / ev_stk64
   (AR_laws_x field 18) and the engine's YGcallHull.stack_hull_vis_x_rng: no hypothesis (HFHULL / HSTK64 are gone). *)

#[local] Notation PRE := (ev_pre (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx).
#[local] Notation MID := (ev_mid (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation REGS := (ev_regs (L := A_prog_listing) (PA := PA)).
#[local] Notation AT_KIND := (ev_at_kind (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation TO_EXIT := (ev_to_exit (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation CFG := (ev_cfg (L := A_prog_listing) (PA := PA)).
#[local] Notation FXOK := (ev_fx (fx := fx)).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation STKa a := (ea_STK (PI := PIA) (L := A_prog_listing) (PA := PA) a).
#[local] Notation sp0a a := (ea_sp0 (L := A_prog_listing) (PA := PA) a).
#[local] Notation S1a a := (ea_S1 (L := A_prog_listing) (PA := PA) a).
#[local] Notation fra a := (ea_fr (L := A_prog_listing) (PA := PA) a).
#[local] Notation FPa a := (ea_FP (L := A_prog_listing) (PA := PA) a).
#[local] Notation lena a := (ea_len (L := A_prog_listing) (PA := PA) a).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* STAND-IN: the ex_string walk (the kit's text tex_string_specX, PRH_FnEx.v; owner the unit owner's S8b lane), at every float
   state (ex_string reaches no float instruction; the unit owner ruled the forall fx1 form) *)
Hypothesis STRX : forall fx1, tex_string_specX (fx := fx1) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
(* STAND-IN, owner c-libc-stdio: the strcmp row at __wrap_strcmp (`jal wrapper_strcmp` at 0x83528), at every float
   state, in its xrom form YGcallMxmn.astrcmp_realizes_xrom: its read-only premise is arodata_okP over the call's view
   (supplied from ev_pre by S8aWord.ev_rod) and its post keeps memnorm. The text pieces 7 + 8 take (S8aItemsTop.v SCMP).
   Supplier on #102: ps_strcmp_xrom_A / ps_strcmp_xrom_xs_A (lib/A/PSstrRo.v blob 4de202368a14, on int102 and on this
   base; engine YGcallMxmn b47cf7942c3d over Spec/PresetRodata 4eb7e95e7e93). It replaces CMP
   (YGcallMx.astrcmp_realizes_x), whose rom_view premise needed the false HROM. *)
Hypothesis SCMP : forall fx1 : YK11.FPState, YGcallMxmn.astrcmp_realizes_xrom (fx := fx1) SEGS B ARx
  (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) (SIGMA AS___wrap_strcmp).
(* STAND-IN, discharged at the preset instance by block_amem_range8_cf (the cf layer writer, 6c9f248bed97 YGcfBlockRange.v:46;
   ablocks = the blocks' sptr_addr form): strcmp's amem_range8 for v->str and in->scratch. A law of ARx's live blocks,
   no image fact. *)
Hypothesis HAM8 : forall ly S Hp W mem md p n k, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= k <= n ->
  amem_range8 p (k + 1).

(* S8aDisp's ev_cfg_to (Section-local there and in S8aWord, so restated) *)
Ltac ev_cfg_to off :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 (pa_val A_TEXT + ?n)) ?m _; cfg_model := ?d |} _ =>
    rewrite (ev_cfg_eq _ r off m d n ltac:(rewrite ev_pc_eq; vm_compute; reflexivity)) end.

(* the return site of `jal ex_string` (LENGTH, offset from ex_value's entry) *)
Definition EV_SRET : Z := 0x230.   (* 0x834d4: `bnez a0, 0x83d48` *)

(* H4 (string): the text's outcome (ev_out) from ex_string's reading and, for a string read, the differs bit *)
Lemma ev_string_out : forall a i1 r p' dl',
  (i1 < length (ea_x a))%nat -> nth i1 (ea_x a) 0 = 34 ->
  PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = skipn i1 (ea_x a) ->
  (ea_dl a = 0 \/ ea_dl a = 1) -> 0 <= ea_dep a <= 32 ->
  match fst (fst (PjGrammar.jr_string (skipn (Nat.succ i1) (ea_x a)) [])) with
  | None => r = -1 /\ p' = Z.of_nat i1 /\ dl' = ea_dl a
  | Some (s, rest) => r = 0 /\ p' = Z.of_nat (length (ea_x a)) - Z.of_nat (length rest) /\ (dl' = 0 \/ dl' = 1) /\
      (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> PjTree.JStr s))
  end ->
  ev_out (L := A_prog_listing) (PA := PA) a r p' (ea_dep a) dl'.
Proof.
intros a i1 r p' dl' Hi Hc Hsk Hdl Hdep H.
assert (HV : prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
  match fst (fst (PjGrammar.jr_string (skipn (Nat.succ i1) (ea_x a)) [])) with
  | None => None | Some (s, r) => Some (PjTree.JStr s, r) end).
{ apply ev_V_str. rewrite Hsk, (ev_skipn_cons _ i1 Hi), Hc. reflexivity. }
unfold ev_out. rewrite HV.
destruct (fst (fst (PjGrammar.jr_string (skipn (Nat.succ i1) (ea_x a)) []))) as [[s rest]|].
- destruct H as (-> & -> & H01 & Hiff). split; [exact H01|]. split; [reflexivity|]. split; [unfold ea_len; reflexivity|].
  split; [reflexivity | exact Hiff].
- destruct H as (-> & -> & ->). split; [exact Hdl|]. split; [reflexivity|]. split; [unfold ea_len; lia | lia].
Qed.

(* the state at the return site of `jal ex_string`: the registers of the cut, a0 = ex_string's result, ev_mid at the
   cursor ex_string left, and the scratch holding the string read *)
Definition ev_sret (a : ev_act) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (i1 : nat) : Prop :=
  REGS a regs /\ getr regs 22 = w64 (fra a) /\ getr regs 23 = w64 (ea_v a) /\ getr regs 27 = w64 (-1) /\
  (i1 < length (ea_x a))%nat /\ nth i1 (ea_x a) 0 = 34 /\
  PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = skipn i1 (ea_x a) /\
  match fst (fst (PjGrammar.jr_string (skipn (Nat.succ i1) (ea_x a)) [])) with
  | None => getr regs 10 = w64 (-1) /\ MID a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a)
  | Some (s, rest) => getr regs 10 = w64 0 /\
      (exists cc, PjGrammar.scan (skipn (Nat.succ i1) (ea_x a)) = Some cc /\ rest = skipn (Nat.succ cc) (skipn (Nat.succ i1) (ea_x a)) /\
         MID a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1 + Z.of_nat cc + 2) (ea_dep a) (ea_dl a)) /\
      bytes_at (PA := PA) W mem (ea_scr a) (s ++ [0])
  end.

(* ---- the call `jal ex_string` (0x834d0): from P_KIND at EV_STR, the run `mv a0, s3; jal`, the text (STRX) by
   aj_call_xWF, back at 0x834d4 in ev_sret ---- *)
Definition ss_str : sstate := mkSS (EV0 + EV_STR) sr_atoms [] None (mkFacts [] [] []).
Lemma ev_str_call : forall a fxc W regs mem md ly S Hp k i1,
  PRE a -> FXOK fxc -> AT_KIND a W regs mem md ly S Hp k i1 34 ->
  SRr SEGS W (CFG fxc regs EV_STR mem md)
    (fun W' c' => exists fx' regs' mem' md' ly' S' Hp' k', c' = CFG fx' regs' EV_SRET mem' md' /\ FXOK fx' /\
       ev_sret a W' regs' mem' md' ly' S' Hp' k' i1).
Proof.
intros a fxc W regs mem md ly S Hp k i1 HP HFX HK.
destruct HK as (HM & HR & H20 & H21 & H22 & H23 & H27 & H11 & H12 & Hi & Hnth & Hws & Hsk).
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & C2 & C3 & C4 & C5).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & HROD & HSH0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinb0 & _ & _ & _ & _ & _ & Hwd0 & Hinbs0 &
  Hd1 & Hd2 & _ & _).
pose proof HAF0 as (HAR0 & _ & _ & Hgp0 & Htp0 & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HM as (HJ & Hwin & EHp & Eab & Hled & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & HRL & HRP & HMN).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
(* the run `mv a0, s3; jal ex_string` *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (HS : st_ok_pi SEGS VAL E ss_str (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (EV0 + EV_STR))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_str. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end. apply awr_ok_nil. }
pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1. clear HF HFr HG.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) N10. prreg HS (1%bv : bv 5) N1.
pmkst HS.
match goal with |- SRr _ _ (mkCfg (YK11.mkst ?r _ ?m _) ?d) _ => set (regsc := r) in *; set (memc := m) in *; set (mdc := d) in * end.
assert (HMc : MID a ly S Hp W memc mdc k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a)).
{ apply (ev_mid_frame B ARx SK LAWS a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ);
    [intros x _; exact (HM1 x) | exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q1) | exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q5) |
     exact HMN]. }
assert (HRc : REGS a regsc) by (apply (ev_regs_kept a regs _ HR); intros r0 Hr0; apply HK; cbv in Hr0 |- *; tauto).
clear HM HJ Hwin EHp Eab Hled Hcur Hsrc Hwd Htree Hsav Hflag HRL HRP HMN Q1 Q2 Q3 Q4 Q5 Hpres HAR Hly Etop Eslo Eshi.
pose proof HMc as (HJ & Hwin & EHp & Eab & Hled & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & HRL & HRP & HMN).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
assert (R2c : getr regsc 2 = w64 (S1a a)) by (rewrite (HK 2%bv) by (cbv; tauto); exact R2).
assert (ES1 : spZ regsc = S1a a) by (unfold spZ; rewrite R2c; apply unsigned_lit_small; lia).
assert (HSTKs : (0 <=? STK_ex_string (PI := PIA)) && (STK_ex_string (PI := PIA) <=? 16384) = true) by (vm_compute; reflexivity).
apply andb_prop in HSTKs as [HSs1 HSs2]. apply Z.leb_le in HSs1. apply Z.leb_le in HSs2.
set (spJ := sp0a a + ea_d a) in *.
assert (Ho16 : (S1a a - spJ) mod 16 = 0 /\ (spJ - S1a a) mod 16 = 0).
{ unfold spJ. pose proof (Z.div_mod (S1a a) 32 ltac:(lia)). pose proof (Z.div_mod (sp0a a) 16 ltac:(lia)).
  pose proof (Z.div_mod (ea_d a) 16 ltac:(lia)).
  split.
  - replace (S1a a - (sp0a a + ea_d a)) with ((2 * (S1a a / 32) - sp0a a / 16 - ea_d a / 16) * 16) by lia.
    apply Z.mod_mul. lia.
  - replace (sp0a a + ea_d a - S1a a) with ((sp0a a / 16 + ea_d a / 16 - 2 * (S1a a / 32)) * 16) by lia.
    apply Z.mod_mul. lia. }
destruct (ev_call_st fxc SEGS (w_H W) regsc (SIGMA AS_ex_string) memc spJ (S1a a - spJ)) as (E0 & ss0 & HS0 & Hrv0 & Hpc0 & Hsp0 & HE2).
{ unfold spJ. lia. }
{ rewrite R2c. unfold w64. f_equal. lia. }
destruct (ev_chain B ARx SK a ly S Hp W memc mdc _ _ _ _ (S1a a) HP HMc ltac:(lia)) as (ch1 & Hch1).
set (FP1 := [(ea_scr a, ea_scr a + lena a + 1); (ea_q a, ea_q a + 8)]).
pose proof (ev_rod B ARx SK LAWS a ly S Hp W memc mdc _ _ _ _ HP HMc) as Hrod.
assert (Hwin' : fwin ly W regsc memc (spJ - S1a a)).
{ split; [lia|]. split; [exact (proj2 Ho16)|]. split; [rewrite ES1, Etop; unfold spJ; lia|].
  intros z Hz. rewrite ES1 in Hz. apply Hpres. unfold spJ in *. lia. }
assert (Hinb : prhex_inblk B ly S Hp (ea_x0 a) (lena a)) by (unfold prhex_inblk; rewrite EHp, Eab; exact (Hinb0 ltac:(unfold ea_len; lia))).
assert (Hinbs : prhex_inblk B ly S Hp (ea_scr a) (lena a + 1)) by (unfold prhex_inblk; rewrite EHp, Eab; exact Hinbs0).
assert (Hwd' : wdest_ok (PA := PA) B (STK_ex_string (PI := PIA)) ly S W regsc memc (ea_scr a) (lena a + 1)).
{ destruct Hwd as (W0' & W1' & W2' & W3' & W4' & W5').
  split; [exact W0'|]. split; [exact W1'|]. split; [exact W2'|]. split; [|split; [exact W4' | exact W5']].
  intros z Hz. destruct (W3' z Hz) as (Hzw & Hzo & _). split; [exact Hzw|]. split; [exact Hzo|].
  rewrite ES1. unfold ea_len in *. lia. }
assert (Hi1 : 0 <= Z.of_nat i1 < Z.of_nat (length (ea_x a))) by lia.
(* PRH_Base.fpre's two conjuncts past the read-only view (walkkit old-pin be60d536d2af): ex_string's entry sp is the
   body's S1, 64 or more below the stack's top (S1 <= sp0 - 256 and fpre's sp0 + 64 <= ly_stk_hi at the activation);
   its ra is the jal's return pc, a listing literal below the ceiling's least value *)
assert (HSPc : spZ regsc + 64 <= ly_stk_hi ly).
{ rewrite ES1, Eshi. change (spZ (ea_regs a)) with (sp0a a) in HSH0. lia. }
assert (HRAc : raZ regsc < YM05.alloc_ceiling).
{ unfold raZ. rewrite N1. apply (Z.lt_le_trans _ 0x7fff7f800000); [apply Z.ltb_lt; vm_compute; reflexivity | lia]. }
eapply SRr_bind.
{ eapply (aj_call_xWF_d (fx := fxc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ A_prog_listing PA) W E0 ss0
    (@YK11.mkst fxc regsc (Z_to_bv 64 (SIGMA AS_ex_string)) memc (YK11.seg_rom SEGS))
    (STKa a + ea_d a) spJ (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)]
    ly S Hp mdc _ (STK_ex_string (PI := PIA)) FP1 (S1a a - spJ) (spJ - S1a a) (Z_to_bv 64 spJ)
    (getr regsc 1) ch1 _ HS0 Hrv0 HJ).
  - exact Hsp0.
  - exact HE2.
  - apply unsigned_lit_small. unfold spJ. lia.
  - exact (proj1 Ho16).
  - lia.
  - lia.
  - unfold spJ. rewrite EK. lia.
  - lia.
  - lia.
  - cbn [ms_regs YK11.mkst]. rewrite (HK 3%bv) by (cbv; tauto). rewrite R3. exact Hgp0.
  - cbn [ms_regs YK11.mkst]. rewrite (HK 4%bv) by (cbv; tauto). rewrite R4. exact Htp0.
  - reflexivity.
  - rewrite N1. apply (ret_ok_codeptr_v (PI := PA)); [split; apply Z.leb_le || apply Z.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity].
  - rewrite N1. rewrite unsigned_lit_small; [apply Z.leb_le; vm_compute; reflexivity|].
    split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
  - cbn [ms_regs ms_mem YK11.mkst]. replace (spJ + (S1a a - spJ)) with (S1a a) by lia.
    unfold s0Z. rewrite (HK 8%bv) by (cbv; tauto). rewrite R8, unsigned_lit_small by lia. exact Hch1.
  - intros HAFN. rewrite Hpc0. eapply SRr_mono.
    + exact (STRX fxc ly S Hp W regsc memc mdc ch1 (ea_q a) (ea_x0 a) (Z.of_nat i1) (ea_scr a) (spJ - S1a a)
        (ea_x a) (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a)
        (conj HAFN (conj Hrod (conj HSPc (conj HRAc (proj1 HFX))))) ltac:(rewrite N10; exact E19) Q1 Q2 Q4 Hqm ltac:(rewrite ES1; lia)
        ltac:(rewrite ES1; unfold spJ; lia) Hwin' Hsrc Hinb ltac:(unfold ea_len in Hlen; exact Hlen) Hi1 Hwd' Hinbs
        Hd1 Hd2 Hled).
    + cbv beta. intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k' & -> & HJc & HXc & HPr & HQ).
      exists fxc, ly', S', Hp', regs', mem', md', k'. split; [reflexivity|]. split; [exact (proj1 HFX)|].
      split; [intros r0 _; reflexivity|]. split; [exact HJc|]. split; [exact HPr|]. exact (conj HXc HQ).
  - intros z (r0 & Hin & Hr0). left. exists r0. split; [|exact Hr0]. unfold FP1 in Hin. unfold ea_FP.
    cbn [In] in Hin |- *. destruct Hin as [<-|[<-|[]]]; tauto. }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJo & HJc & HPr &
  (HXc & (HRLc & EHp2 & ES2 & Eab2 & Hled2 & Hcase) & HMNk)).
pose proof (HMNk HMN) as HMN2.
apply SRr_ret.
exists fx2, regs2, mem2, md2, ly2, S2, Hp2, (k + k1).
split.
{ (* 7924 (DERIVED: the return pc's listing position, 0x834d4 - A_prog_base 0x815e0 on A') *)
  rewrite N1. replace 7924 with (EV0 + EV_SRET) by (vm_compute; reflexivity).
  apply ev_cfg_eq. rewrite ev_pc_eq. reflexivity. }
split.
{ split; [exact HFZ|]. intros rr Hrr. rewrite (HFK rr Hrr). exact (proj2 HFX rr Hrr). }
destruct (ev_regs_call a regsc regs2 HRc HPr) as (HR2 & E22).
replace (spJ + (S1a a - spJ) + (spJ - S1a a)) with spJ in HJc by lia.
assert (HX' : forall z, S1a a <= z < sp0a a + ea_d a -> ~ inFP FP1 z ->
          aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) memc z)
  by (intros z Hz Hn; apply HXc; [rewrite ES1; unfold spJ in *; lia | exact Hn]).
assert (HFP1 : forall z, inFP FP1 z -> inFP (FPa a) z).
{ intros z (r0 & Hin & Hr0). exists r0. split; [|exact Hr0]. unfold FP1 in Hin. unfold ea_FP.
  cbn [In] in Hin |- *. destruct Hin as [<-|[<-|[]]]; tauto. }
assert (HFPq : forall z, ea_q a + 8 <= z < ea_q a + 32 -> ~ inFP FP1 z).
{ intros z Hz (r0 & Hin & Hr0). unfold FP1 in Hin. cbn [In] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr0;
    unfold ea_len in *; lia. }
assert (HdlK : val_mem SEGS (rdW W2 mem2) (ea_q a + 32) 4 (ea_dl a)).
{ eapply ev_vm_kept; [|exact Q5]. intros kk Hk. apply mbyte_of_aview. apply HX'; [unfold ea_len in *; lia|].
  intros (r0 & Hin & Hr0). unfold FP1 in Hin. cbn [In] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr0;
    unfold ea_len in *; lia. }
assert (VMS : forall z (n : nat) v, prhex_same (PA := PA) W memc W2 mem2 z (Z.of_nat n) ->
          val_mem SEGS (rdW W memc) z n v -> val_mem SEGS (rdW W2 mem2) z n v).
{ intros z n v Hs Hv. eapply ev_vm_kept; [|exact Hv]. intros kk Hk. apply mbyte_of_aview. apply Hs. lia. }
split; [exact HR2|]. split; [rewrite E22, (HK 22%bv) by (cbv; tauto); exact H22|].
split.
{ assert (H23r : getr regs2 23 = getr regsc 23) by exact (HPr 23 ltac:(unfold acallee_saved; lia)).
  rewrite H23r, (HK 23%bv) by (cbv; tauto). exact H23. }
split.
{ assert (H27r : getr regs2 27 = getr regsc 27) by exact (HPr 27 ltac:(unfold acallee_saved; lia)).
  rewrite H27r, (HK 27%bv) by (cbv; tauto). exact H27. }
split; [exact Hi|]. split; [exact Hnth|]. split; [exact Hsk|].
rewrite Nat2Z.id in Hcase.
destruct (fst (fst (PjGrammar.jr_string (skipn (Nat.succ i1) (ea_x a)) []))) as [[s rest]|].
- destruct Hcase as (Ha0 & (cc & Hsc & Hrest & Hqv) & Hby).
  split; [exact Ha0|]. split; [|exact Hby].
  exists cc. split; [exact Hsc|]. split; [exact Hrest|].
  exact (ev_mid_rt B ARx SK LAWS HSHD a ly S Hp W memc mdc _ _ _ _ ly2 S2 Hp2 W2 mem2 md2 _ _ FP1 k1 _ _ HP HMc
    HJo HJc HX' HFP1 HFPq EHp2 Eab2 Hled2 Hqv HdlK ltac:(unfold ea_len; lia) HRLc
    ltac:(first [rewrite ES2 | rewrite <- ES2]; apply PresetHullBudget.hull_used_refl)
    ltac:(intros; first [rewrite ES2 | rewrite <- ES2]; assumption) HMN2).
- destruct Hcase as (Ha0 & Hsq).
  split; [exact Ha0|].
  exact (ev_mid_rt B ARx SK LAWS HSHD a ly S Hp W memc mdc _ _ _ _ ly2 S2 Hp2 W2 mem2 md2 _ _ FP1 k1 _ _ HP HMc
    HJo HJc HX' HFP1 HFPq EHp2 Eab2 Hled2 (VMS _ 8%nat _ Hsq Q1) HdlK
    ltac:(unfold ea_len; lia) HRLc ltac:(first [rewrite ES2 | rewrite <- ES2]; apply PresetHullBudget.hull_used_refl)
    ltac:(intros; first [rewrite ES2 | rewrite <- ES2]; assumption) HMN2).
Qed.

(* ---- after ex_string: the two short exits. a0 = -1: `bnez a0, 0x83d48` (s11 = -1 of the cut); a0 = 0 and v = 0:
   `beqz s7, 0x83cb0; li s11, 0; j 0x83d48` ---- *)
Definition ss_snone : sstate := mkSS (EV0 + EV_SRET) (sr_set sr_atoms 10%bv (SLit 18446744073709551615)) [] None (mkFacts [] [] []).
Definition ss_sv0 : sstate := mkSS (EV0 + EV_SRET) (sr_set (sr_set sr_atoms 10%bv (SLit 0)) 23%bv (SLit 0)) [] None (mkFacts [] [] []).

Lemma ev_str_none : forall a fx' W regs mem md ly S Hp k i1,
  PRE a -> FXOK fx' -> MID a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) -> REGS a regs ->
  getr regs 22 = w64 (fra a) -> getr regs 27 = w64 (-1) -> getr regs 10 = w64 (-1) ->
  ev_out (L := A_prog_listing) (PA := PA) a (-1) (Z.of_nat i1) (ea_dep a) (ea_dl a) ->
  SRr SEGS W (CFG fx' regs EV_SRET mem md) (TO_EXIT a).
Proof.
intros a fx' W regs mem md ly S Hp k i1 HP HFX HM HR H22 H27 H10 Hout.
pose proof HM as (HJ & _ & _ & _ & _ & (Q1 & _ & _ & _ & Q5) & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_snone (restrict (w_H W) (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + (EV0 + EV_SRET))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_snone. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | discriminate | rewrite H10; apply bv_eq; reflexivity].
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUNTOI := @paj_run_to_x_inv fx' rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_EXIT).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end. apply awr_ok_nil. }
pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi E _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26; 27]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
pmkst HS. ev_cfg_to EV_EXIT.
apply SRr_ret.
lazymatch goal with |- TO_EXIT a W (CFG fx' ?r EV_EXIT ?m ?d) => exists fx', r, m, d, ly, S, Hp end.
eexists. exists (-1), (Z.of_nat i1), (ea_dep a), (ea_dl a). split; [reflexivity|]. split; [exact HFX|].
split.
{ apply (ev_mid_frame B ARx SK LAWS a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ).
  - intros x _. exact (HM1 x).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q1).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q5).
  - exact HMN. }
split; [apply (ev_regs_kept a regs _ HR); intros r0 Hr0; apply HK; cbv in Hr0 |- *; tauto|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact H22|].
split; [rewrite (HK 27%bv) by (cbv; tauto); exact H27|].
exact Hout.
Qed.

Lemma ev_str_v0 : forall a fx' W regs mem md ly S Hp k p',
  PRE a -> FXOK fx' -> MID a ly S Hp W mem md k (ea_x0 a + p') (ea_dep a) (ea_dl a) -> REGS a regs ->
  getr regs 22 = w64 (fra a) -> getr regs 10 = w64 0 -> getr regs 23 = w64 0 ->
  ev_out (L := A_prog_listing) (PA := PA) a 0 p' (ea_dep a) (ea_dl a) ->
  SRr SEGS W (CFG fx' regs EV_SRET mem md) (TO_EXIT a).
Proof.
intros a fx' W regs mem md ly S Hp k p' HP HFX HM HR H22 H10 H23 Hout.
pose proof HM as (HJ & _ & _ & _ & _ & (Q1 & _ & _ & _ & Q5) & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_sv0 (restrict (w_H W) (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + (EV0 + EV_SRET))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sv0. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [|discriminate|rewrite H23; reflexivity].
    apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | discriminate | rewrite H10; reflexivity].
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUNTOI := @paj_run_to_x_inv fx' rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_EXIT).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end. apply awr_ok_nil. }
pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi E _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27.
pmkst HS. ev_cfg_to EV_EXIT.
apply SRr_ret.
lazymatch goal with |- TO_EXIT a W (CFG fx' ?r EV_EXIT ?m ?d) => exists fx', r, m, d, ly, S, Hp end.
eexists. exists 0, p', (ea_dep a), (ea_dl a). split; [reflexivity|]. split; [exact HFX|].
split.
{ apply (ev_mid_frame B ARx SK LAWS a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ).
  - intros x _. exact (HM1 x).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q1).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q5).
  - exact HMN. }
split; [apply (ev_regs_kept a regs _ HR); intros r0 Hr0; apply HK; cbv in Hr0 |- *; tauto|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact H22|].
split; [rewrite N27; reflexivity|].
exact Hout.
Qed.

(* ---- the v <> 0 tail after ex_string read a string s (0x834d4 with a0 = 0): v's shadow, v->type, the shadow of
   v + 16 and q + 24, `jal wrapper_strcmp` (CMP), and in->differs (0x83530-0x83550) or not (0x83cb0), to P_EXIT ---- *)
Definition ev_str_vn_stmt : Prop :=
  forall a fx' W regs mem md ly S Hp k p' s,
  PRE a -> FXOK fx' -> MID a ly S Hp W mem md k (ea_x0 a + p') (ea_dep a) (ea_dl a) -> REGS a regs ->
  getr regs 22 = w64 (fra a) -> getr regs 10 = w64 0 -> getr regs 23 = w64 (ea_v a) -> ea_v a <> 0 ->
  bytes_at (PA := PA) W mem (ea_scr a) (s ++ [0]) -> Forall (fun b => 0 < b < 256) s ->
  (length s <= length (ea_x a))%nat ->
  (forall dl', (dl' = 0 \/ dl' = 1) -> (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> PjTree.JStr s)) ->
     ev_out (L := A_prog_listing) (PA := PA) a 0 p' (ea_dep a) dl') ->
  SRr SEGS W (CFG fx' regs EV_SRET mem md) (TO_EXIT a).

(* ======== the v <> 0 tail: small byte / view lemmas ======== *)
(* COPIED from lane E's S8aNumE.v eve_byte_eq (da73e1570f8) *)
Lemma vn_byte_eq : forall v (n k : nat), (k < n)%nat -> (n <= 8)%nat ->
  Z_to_bv 8 (YG0f.le_byte v n k) = byte_of_word (Z_to_bv 64 v) (Z.of_nat k).
Proof.
intros v n k Hk Hn. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). unfold YG0f.le_byte.
apply Z.bits_inj'. intros jj Hj. change 256 with (2 ^ 8). rewrite !Z.testbit_mod_pow2 by lia.
destruct (jj <? 8) eqn:Ej; [|reflexivity]. apply Z.ltb_lt in Ej.
rewrite !Z.shiftr_spec by lia. rewrite !Z.testbit_mod_pow2 by lia.
replace (jj + 8 * Z.of_nat k <? 8 * Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; nia).
replace (jj + 8 * Z.of_nat k <? 64) with true by (symmetry; apply Z.ltb_lt; nia). reflexivity.
Qed.
(* COPIED from lane E's S8aNumE.v eve_chunk_val (da73e1570f8), at SEGS *)
Lemma vn_chunk_val : forall E m base off (w : N) e v, (w <= 8)%N -> sv_denot E e = Z_to_bv 64 v ->
  val_mem SEGS m (base + off) (N.to_nat w) v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)).
Proof.
intros E m base off w e v Hw He Hv i Hi. unfold YP09.c_len, YP09.cv_len in Hi. cbn [YP09.c_val YP09.c_off] in *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
pose proof (Hv (Z.to_nat i) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. rewrite H.
f_equal. rewrite He. replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia. apply vn_byte_eq; lia.
Qed.
(* COPIED from lane E's S8aNumE.v eve_val_of_chunk (da73e1570f8), at SEGS *)
Lemma vn_val_of_chunk : forall E m base off (w : N) e, (w <= 8)%N ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) ->
  val_mem SEGS m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros E m base off w e Hw Hc k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len, YP09.cv_len; cbn [YP09.c_val]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
pose proof (vn_byte_eq (bv_unsigned (sv_denot E e)) (N.to_nat w) k Hk ltac:(lia)) as Hb.
rewrite Z_to_bv_bv_unsigned in Hb. symmetry. exact Hb.
Qed.
(* COPIED from lane E's S8aNumE.v evE_chunk_of_st (da73e1570f8); its float state fxc (a class instance) makes the
   machine state's float state generic *)
Lemma vn_chunk_of_st : forall (fxc : YK11.FPState) E ss (ms : machine_state) (W : world SEGS) i r jj off (w : N) e,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> nth_error (YP09.r_chunks r) jj = Some (YP09.mkChunk off (CVal w e)) ->
  (w <= 8)%N ->
  val_mem SEGS (rdW W (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros fxc E ss ms W i r jj off w e HS Hr Hc Hw.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hall & _).
pose proof (proj1 (Forall_forall _ _) Hall r (nth_error_In _ i Hr)) as Hro.
destruct Hro as (_ & _ & _ & Hch).
pose proof (proj1 (Forall_forall _ _) Hch _ (nth_error_In _ jj Hc)) as Hck.
cbn [ms_mem restrict] in Hck |- *.
exact (vn_val_of_chunk E _ _ off w e Hw Hck).
Qed.
(* the same at a raw st_ok (the engine's state at a call stop) *)
Lemma vn_chunk_of_st' : forall (fxc : YK11.FPState) E ss (ms : machine_state) (W : world SEGS) i r jj off (w : N) e,
  st_ok SEGS E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> nth_error (YP09.r_chunks r) jj = Some (YP09.mkChunk off (CVal w e)) ->
  (w <= 8)%N ->
  val_mem SEGS (rdW W (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros fxc E ss ms W i r jj off w e HS Hr Hc Hw.
pose proof (st_ok_mem_ok SEGS E ss (restrict (w_H W) ms) HS) as (_ & Hall & _).
pose proof (proj1 (Forall_forall _ _) Hall r (nth_error_In _ i Hr)) as Hro.
destruct Hro as (_ & _ & _ & Hch).
pose proof (proj1 (Forall_forall _ _) Hch _ (nth_error_In _ jj Hc)) as Hck.
cbn [ms_mem restrict] in Hck |- *.
exact (vn_val_of_chunk E _ _ off w e Hw Hck).
Qed.
(* COPIED from lane E's S8aNumE.v evE_frame_aview (da73e1570f8) *)
Lemma vn_frame_aview : forall E rs (W : world SEGS) m m' z,
  frame_of E rs (rdW W m) (rdW W m') -> 0 <= z < 2 ^ 64 -> ~ YP09.in_wrange E rs z ->
  aview SEGS (w_H W) m' z = aview SEGS (w_H W) m z.
Proof.
intros E rs W m m' z HF Hz Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 z)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* COPIED from lane E's S8aNumE.v eve_garr8_aview, eve_first_byte, eve_src_ok, eve_str_eq (da73e1570f8), at SEGS *)
Lemma vn_garr8_aview : forall (H : word -> bool) m p l j, garr8 SEGS (mrestrict H m) p l -> (j < length l)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H m p l j Hg Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j Hg Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. exact (proj2 (Hg j Hj)).
Qed.
Lemma vn_first_byte : forall (W : world SEGS) m p l, garr8 SEGS (mrestrict (w_H W) m) p (l ++ [0]) ->
  Forall (fun c => c <> 0) l -> first_byte SEGS W m p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
  intros W m p l Hg Hnz. split; [lia|]. split.
  - intros i Hi. exists (nth (Z.to_nat i) l 0). split.
    + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
      rewrite (vn_garr8_aview (w_H W) m p (l ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
      rewrite app_nth1 by lia. reflexivity.
    + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
  - intros _. rewrite (vn_garr8_aview (w_H W) m p (l ++ [0]) (length l) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma vn_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
  intros W regs m p l Hg Hw a Ha. split; [|exact (Hw a Ha)].
  replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
  rewrite (vn_garr8_aview (w_H W) m p l (Z.to_nat (a - p)) Hg) by lia. discriminate.
Qed.
Lemma vn_str_eq : forall (H : word -> bool) m p1 p2 l1 l2,
  garr8 SEGS (mrestrict H m) p1 (l1 ++ [0]) -> garr8 SEGS (mrestrict H m) p2 (l2 ++ [0]) ->
  ((Z.of_nat (length l1) = Z.of_nat (length l2) /\
    forall i, 0 <= i < Z.of_nat (length l1) -> aview SEGS H m (p1 + i) = aview SEGS H m (p2 + i)) <-> l1 = l2).
Proof.
  intros H m p1 p2 l1 l2 G1 G2. split.
  - intros (Hl & Heq). apply (nth_ext l1 l2 0 0); [lia|]. intros jj Hj.
    pose proof (Heq (Z.of_nat jj) ltac:(lia)) as E.
    rewrite (vn_garr8_aview H m p1 (l1 ++ [0]) jj G1) in E by (rewrite length_app; cbn; lia).
    rewrite (vn_garr8_aview H m p2 (l2 ++ [0]) jj G2) in E by (rewrite length_app; cbn; lia).
    rewrite app_nth1 in E by lia. rewrite app_nth1 in E by lia. injection E as E. exact E.
  - intros <-. split; [reflexivity|]. intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (vn_garr8_aview H m p1 (l1 ++ [0]) _ G1), (vn_garr8_aview H m p2 (l1 ++ [0]) _ G2)
      by (rewrite length_app; cbn; lia). reflexivity.
Qed.
(* COPIED from lane E's S8aNumE.v evE_br_eq_t / evE_br_eq_f (da73e1570f8): a call's result tested against 0 *)
Lemma vn_br_eq_t : forall E n (w : word), ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> w = w64 0.
Proof.
intros E n w Hw Hc. rewrite branch_eq_U, U_SOff, U_SLit, Hw in Hc.
apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite zcanon_id in Hc by (unfold M64; lia).
apply bv_eq. transitivity 0; [lia | reflexivity].
Qed.
Lemma vn_br_eq_f : forall E n (w : word), ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> w <> w64 0.
Proof.
intros E n w Hw Hc ->. rewrite branch_eq_U, U_SOff, U_SLit, Hw in Hc. vm_compute in Hc. discriminate.
Qed.
(* an engine shadow obligation at an atom n + c is a sub-range of an addressable window *)
Lemma vn_obl : forall (W : world SEGS) mem E n c x len a0 n0,
  ew E 24%nat = w64 SHADOW_OFF -> ew E n = w64 x -> 0 <= x -> x + c + len <= 2 ^ 47 -> 0 <= c -> 0 <= len ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a0 n0 -> a0 <= x + c -> x + c + len <= a0 + n0 ->
  range_addressable (rd_of SEGS (rdW W mem)) (U E D_Bx) (U E (SOff n c)) len.
Proof.
intros W mem E n c x len a0 n0 H24 Hn Hx0 Hx1 Hc Hl HR H1 H2.
unfold D_Bx. rewrite !U_SOff, H24, Hn. unfold w64.
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia). rewrite Z.add_0_r.
change (rd_of SEGS (rdW W mem)) with (aview SEGS (w_H W) mem).
exact (range_addressable_sub _ _ a0 n0 (x + c) len HR H1 H2).
Qed.
(* strcmp's amem_range8 for a string inside a live block (HAM8 at k := x - p + kx, start shifted to x) *)
Lemma vn_am8 : forall ly S Hp W mem md p n x kx, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> 0 <= kx -> x + kx <= p + n -> amem_range8 x (kx + 1).
Proof.
intros ly S Hp W mem md p n x kx HAR Hin Hpx Hkx Hxe.
pose proof (HAM8 ly S Hp W mem md p n (x - p + kx) HAR Hin ltac:(lia)) as H.
unfold amem_range8 in *. lia.
Qed.
(* strcmp's granule-tail premise for a string whose NUL x + k lies inside a live block: the block's bytes are present
   (alx_blocks), the bytes after its end up to the granule's end too (alx_blocks_tail) *)
Lemma vn_tail : forall ly S Hp W mem md p n x k, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> 0 <= k -> x + k < p + req_size n ->
  forall z, x + k < z < x + k - (x + k) mod 8 + 8 -> aview SEGS (w_H W) mem z <> None.
Proof.
intros ly S Hp W mem md p n x k HAR Hin Hpx Hk Hxe z Hz.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpr & _).
destruct (Z_lt_le_dec z (p + req_size n)) as [Hlt|Hge].
- destruct (Hpr z ltac:(lia)) as (Hpa & _). exact (aview_some_of_apresent SEGS _ _ _ Hpa).
- apply (alx_blocks_tail SEGS B ARx LAWS _ _ _ _ _ _ _ _ z HAR Hin). split; [exact Hge|].
  pose proof (Z.div_mod (x + k) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)) as M1.
  assert (H8 : (x + k) / 8 + 1 <= (p + req_size n + 7) / 8).
  { assert ((x + k) / 8 <= (p + req_size n - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (E7 : (p + req_size n - 1) / 8 + 1 = (p + req_size n + 7) / 8).
    { replace (p + req_size n + 7) with ((p + req_size n - 1) + 1 * 8) by lia. rewrite Z.div_add by lia. lia. }
    lia. }
  lia.
Qed.

(* ---- EV_MID when only ev_wr bytes change IN THE VIEW: S8aDisp's ev_mid_frame (raw-memory premise) with the premise
   a call's post gives (aj_strcmp_at_xrom keeps the view, not the raw memory, outside its 2 * ESTACK window); every
   footprint byte of the tree is outside the image (alx_client_img, the image below kLowMemEnd), so its raw byte
   (writability) is kept as well; the memory normal at the new memory (the call's keep) ---- *)
Lemma ev_mid_av : forall a ly S Hp W mem md k p dep dl mem' md' k' p' dl',
  PRE a -> MID a ly S Hp W mem md k p dep dl ->
  AJ (STKa a + ea_d a) (sp0a a + ea_d a) (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly S Hp W mem' md' k' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ ev_wr a z -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  val_mem SEGS (rdW W mem') (ea_q a) 8 p' -> val_mem SEGS (rdW W mem') (ea_q a + 32) 4 dl' ->
  YAkMemnorm.memnorm SEGS mem' ->
  MID a ly S Hp W mem' md' k' p' dep dl'.
Proof.
intros a ly S Hp W mem md k p dep dl mem' md' k' p' dl' HP HM HJ' HAv Hp' Hdl' HMN'.
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinbs0 & _ & _ & Htree0 & _).
destruct HM as (HJ & Hwin & EHp & Eab & Hled & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & HRL & HRP & _).
pose proof HJ' as (HAR' & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
assert (HK : forall z, 0 <= z < 2 ^ 64 -> ~ ev_wr a z ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz Hn. apply mbyte_of_aview. exact (HAv z Hz Hn). }
assert (HKc : forall z, 0 <= z < YM05.alloc_ceiling ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz. apply HK; [zl|]. apply (ev_wr_ceil B ARx); [exact HP | zl]. }
assert (HKa : forall z, 0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z).
{ intros z Hz. apply HAv; [zl|]. apply (ev_wr_ceil B ARx); [exact HP | zl]. }
split; [exact HJ'|].
split.
{ intros z Hz Hn. rewrite <- (Hwin z Hz Hn). apply HAv; [zl|]. exact (ev_wr_win B ARx a z HP Hz Hn). }
split; [exact EHp|]. split; [exact Eab|].
split; [exact (ev_ledger_kept B ARx LAWS ly S Hp W mem mem' mem' md' _ _ _ _ _ _ _ HAR' HKc Hled)|].
split.
{ destruct Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
  split; [exact Hp'|].
  split; [eapply ev_vm_kept; [|exact Q2]; intros kk Hk; apply HK; [zl|]; apply (ev_wr_cur B ARx a _ HP); zl|].
  split; [eapply ev_vm_kept; [|exact Q3]; intros kk Hk; apply HK; [zl|]; apply (ev_wr_cur B ARx a _ HP); zl|].
  split; [eapply ev_vm_kept; [|exact Q4]; intros kk Hk; apply HK; [zl|]; apply (ev_wr_cur B ARx a _ HP); zl|].
  exact Hdl'. }
split.
{ destruct Hsrc as (Hg & H4 & Hc & Ham & Hra & Hhv). unfold ea_len in *.
  split; [|split; [exact H4|split; [exact Hc|split; [exact Ham|split]]]].
  - eapply ev_garr8_kept; [|exact Hg]. intros j Hj. apply HKc. zl.
  - eapply ev_ra_kept; [exact HKa | zl | zl | exact Hra].
  - intros Hl. eapply ev_hull_kept; [exact HKa | zl | exact Hl | zl | exact (Hhv Hl)]. }
split.
{ destruct Hwd as (W0' & W1 & W2 & W3 & W4 & W5). unfold ea_len in *.
  split; [exact W0'|]. split; [exact W1|]. split; [exact W2|]. split.
  - intros z Hz. destruct (W3 z Hz) as (Hwa & Hno & Hns). split; [|split; [exact Hno | exact Hns]].
    destruct Hinbs0 as (b & m & Hbm & Hb & Hbe & _). rewrite <- EHp in *. rewrite <- Eab in Hbm.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem' md' _ _ HAR' Hbm) as (_ & _ & _ & _ & Hpr & _).
    assert (Rm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); zl).
    apply (apresent_writable SEGS). apply (proj1 (Hpr z ltac:(zl))).
  - split.
    + eapply ev_ra_kept; [exact HKa | zl | zl | exact W4].
    + intros Hl. eapply ev_hull_kept; [exact HKa | zl | exact Hl | zl | exact (W5 Hl)]. }
split.
{ destruct Htree0 as [Hv0 | (Ht0 & HDpos & Hfoot)]; [left; exact Hv0|].
  destruct Htree as [Hv0 | (Hpj & Hhome & Hra & Hhv)]; [left; exact Hv0|]. right.
  pose proof (ev_home_bound B ARx LAWS ly S Hp W mem' md' mem' (ea_Lam a) (ea_regs a) (ea_v a) 56 _ _ _ _ _ _ HAR'
    (ev_ledger_kept B ARx LAWS ly S Hp W mem mem' mem' md' _ _ _ _ _ _ _ HAR' HKc Hled) ltac:(rewrite Eshi; zl) ltac:(zl) Hhome) as Hhb.
  (* a byte of a harness block (a Lam entry) is a client byte, outside the image *)
  assert (LI : forall xb kb x, In (xb, kb) (ea_Lam a) -> xb <= x < xb + kb -> ~ in_img SEGS x).
  { intros xb kb x HinL Hx. destruct Hled as (_ & _ & HF & _). rewrite Forall_forall in HF.
    destruct (HF _ HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    pose proof (ev_req_ge (kb + cf_head)). pose proof (@cf_head_nonneg cp).
    apply (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ x HAR'). left. exists (xb - cf_head), (kb + cf_head).
    split; [exact Hab | zl]. }
  (* a footprint byte is a machine address outside the bytes the stretch writes and outside the image *)
  assert (Hfp : forall x, PRH_Reader.pj_footR (ea_v a) (ea_D a) x -> 0 <= x < 2 ^ 64 /\ ~ ev_wr a x /\ ~ in_img SEGS x).
  { intros x Hx. split; [|split].
    - destruct Hx as [Hn | ((xb, kb) & HinD & Hh)]; [zl|].
      pose proof (ev_node_blocks SEGS _ _ _ _ _ Hpj xb kb HinD) as HL. unfold prh_lin in HL.
      destruct Hled as (_ & _ & HF & _). rewrite Forall_forall in HF.
      destruct (HF _ HL) as (Hk0 & Hab & _). cbn [fst snd] in *.
      pose proof (@cf_head_nonneg cp) as Hh0.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem' md' _ _ HAR' Hab) as (_ & Hb4096 & Hbc & _).
      pose proof (req_size_pos (kb + @cf_head cp) ltac:(zl)) as [R1 R2].
      unfold PRH_Reader.pj_holdsR in Hh. cbn [fst snd] in Hh. zl.
    - intros Hw. destruct (Hfoot _ Hx) as (_ & Hnq & Hns & _). unfold ev_wr in Hw. unfold ea_sp0, ea_SA in *. zl.
    - destruct Hx as [Hn | ((xb, kb) & HinD & Hh)].
      + destruct Hhome as [(b & m & HinL & Hb & Hm) | [(cid & pos & HinF & Hb & Hm) | (Hb & Hm)]].
        * exact (LI b m x HinL ltac:(zl)).
        * apply (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ x HAR'). right. left. exists cid, pos. split; [exact HinF | zl].
        * intros Himg. pose proof (@pa_segs_low _ A_prog_listing PA x Himg) as Hlo.
          change (spZ (ea_regs a)) with (sp0a a) in Hb. unfold kLowMemEnd in Hlo. zl.
      + pose proof (ev_node_blocks SEGS _ _ _ _ _ Hpj xb kb HinD) as HL. unfold prh_lin in HL.
        unfold PRH_Reader.pj_holdsR in Hh. cbn [fst snd] in Hh. exact (LI xb kb x HL Hh). }
  split; [|split; [exact Hhome|split]].
  - apply (PRH_Reader.pj_nodeR_frame SEGS (ea_t a) _ _ _ _ _ Hpj).
    intros x Hx. destruct (Hfp x Hx) as (Hr & Hw & Hni).
    split; [exact (HK x Hr Hw)|].
    pose proof (ev_raw_of_aview _ _ _ _ _ Hr Hni (HAv x Hr Hw)) as E.
    intros Hwa. unfold writable_at, LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview in *. rewrite E. exact Hwa.
  - eapply ev_ra_kept; [exact HKa | zl | zl | exact Hra].
  - eapply ev_hull_kept; [exact HKa | zl | zl | zl | exact Hhv]. }
split.
{ unfold ev_saved in *. rewrite Forall_forall in *. intros orr Hin. pose proof (ev_saved_offs orr Hin) as Ho.
  eapply ev_vm_kept; [|exact (Hsav orr Hin)]. intros kk Hk. apply HK; [zl|]. apply (ev_wr_saved B ARx a _ HP). zl. }
split.
{ rewrite <- Hflag. apply rdword_ext. intros kk Hk. apply HKa.
  assert (Hin : In (1, ea_pos a) (frames S)) by (rewrite Hfrs; left; reflexivity).
  destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem' md' HAR') as (_ & HFs). rewrite Forall_forall in HFs.
  destruct (HFs _ Hin) as (F1 & F2). cbn [fst snd] in *.
  assert (Efr : frame_addr ly 1 (ea_pos a) = fra a) by (unfold ea_fr, frame_addr; rewrite EF; reflexivity).
  rewrite Efr in F1, F2. change (fs_frame_bytes 1) with 128 in *. zl. }
split; [exact HRL|]. split; [exact HRP | exact HMN'].
Qed.

(* ---- the symbolic state at 0x834d4 for the v <> 0 tail: a0 = 0, s7 = v <> 0 (atom 23), in at s3 (atom 19), the
   shadow base s8 (atom 24); the region at in: in->scratch (q + 24, atom 32) read, in->differs (q + 32, atom 33)
   written; the region at v: v->type (atom 34) and v->str (v + 16, atom 35) read ---- *)
Definition vn_Rq : YP09.region :=
  YP09.mkRegion (Some 19%nat) 24 36 32 36 [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 4 (SOff 33 0))].
Definition vn_Rv : YP09.region :=
  YP09.mkRegion (Some 23%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0))].
Definition ss_vn : sstate :=
  mkSS (EV0 + EV_SRET) (sr_set sr_atoms 10%bv (SLit 0)) [vn_Rq; vn_Rv] None
    (mkFacts [(19%nat, mkAF D_QLO (2 ^ 47 - 40) 3); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (23%nat, mkAF 0 (2 ^ 47 - 56) 3); (34%nat, mkAF 0 6 0)]
       [mkAC BC_NE (SOff 23 0) (SLit 0)] []).
Ltac vn_ewn := repeat (first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]).

Ltac vn_ewn_in H := repeat (first [rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by lia]).
(* a byte outside the write range of the tail's regions (in at s3 writable on [32, 36), v read-only) *)
Ltac vn_nwr U19 U23 :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; vn_ewn_in Hr;
          rewrite ?U19, ?U23 in Hr; lia |]);
  destruct Hin.
(* the write premise of a run over the tail's regions: in->differs is in the journal's stack window *)
Ltac vn_awr U19 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end;
  eapply awr_ok_cons_gen;
  [ reflexivity | vn_ewn; exact U19 | cbn [YP09.r_wlo YP09.r_whi]; intros ?z ?Hz; left; lia
  | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ].
(* in->differs at the end of a run: the cell q + 32 of the region at in (region 0) *)
Ltac vn_cell HS c HCH :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EE ?ss2 _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss2) 0%nat) in
    lazymatch rr with Some ?r =>
      first [ pose proof (vn_chunk_of_st _ EE ss2 _ _ 0%nat r 0%nat 32 4 c HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
            | pose proof (vn_chunk_of_st _ EE ss2 _ _ 0%nat r 1%nat 32 4 c HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
            | pose proof (vn_chunk_of_st _ EE ss2 _ _ 0%nat r 2%nat 32 4 c HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH ]
    end
  | st_ok _ ?EE ?ss2 _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ss2) 0%nat) in
    lazymatch rr with Some ?r =>
      first [ pose proof (vn_chunk_of_st' _ EE ss2 _ _ 0%nat r 0%nat 32 4 c HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
            | pose proof (vn_chunk_of_st' _ EE ss2 _ _ 0%nat r 1%nat 32 4 c HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
            | pose proof (vn_chunk_of_st' _ EE ss2 _ _ 0%nat r 2%nat 32 4 c HS ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH ]
    end
  end.
Lemma vn_lit : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (sv_denot E (SLit z)) = z.
Proof. intros E z Hz. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)). rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.
(* P_EXIT with r = 0 *)
Lemma vn_exit : forall a fx' W regs' mem' md' ly S Hp k' p' dl',
  FXOK fx' -> MID a ly S Hp W mem' md' k' (ea_x0 a + p') (ea_dep a) dl' -> REGS a regs' ->
  getr regs' 22 = w64 (fra a) -> getr regs' 27 = w64 0 -> ev_out (L := A_prog_listing) (PA := PA) a 0 p' (ea_dep a) dl' ->
  SRr SEGS W (CFG fx' regs' EV_EXIT mem' md') (TO_EXIT a).
Proof.
intros a fx' W regs' mem' md' ly S Hp k' p' dl' HFX HM HR H22 H27 Hout. apply SRr_ret.
exists fx', regs', mem', md', ly, S, Hp, k', 0, p', (ea_dep a), dl'.
split; [reflexivity|]. split; [exact HFX|]. exact (conj HM (conj HR (conj H22 (conj H27 Hout)))).
Qed.

(* ======== THE v <> 0 TAIL (0x834d4-0x83550, 0x83cb0-0x83cb4; the ASan report arms are absorbed by the engine) ======== *)
Lemma ev_str_vn : ev_str_vn_stmt.
Proof.
unfold ev_str_vn_stmt.
intros a fx' W regs mem md ly S Hp k p' s HP HFX HM HR H22 H10 H23 Hvn Hby Hsb Hsl Hout.
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hch.
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & HROD & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwd0 & Hinbs0 &
  Hd1 & Hd2 & Htree0 & Hled0 & _).
pose proof HAF0 as (HAR0 & _ & _ & Hgp0 & Htp0 & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HM as (HJ & Hwin & EHp & Eab & Hled & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & HRL & HRP & HMN).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof Hwd as (Hscr0 & Hscrc & _ & _ & HWra & HWhv).
destruct Htree as [Hv0 | (Hpj & Hhome & Hrav & Hhv)]; [contradiction|].
destruct Htree0 as [Hv0 | (_ & _ & Hfoot)]; [contradiction|].
destruct (ev_hdrR _ _ _ _ _ _ Hpj) as (str & (Htg32 & Htgv) & Hv8 & (Hstr64 & Hstrv) & Hcs).
pose proof (ev_home_bound B ARx LAWS ly S Hp W mem md mem (ea_Lam a) (ea_regs a) (ea_v a) 56 _ _ _ _ _ _ HAR Hled
  ltac:(rewrite Eshi; lia) ltac:(lia) Hhome) as (Hvlo & Hvhi).
assert (Hvq : ea_q a + 40 <= ea_v a \/ ea_v a + 56 <= ea_q a).
{ destruct (Z_le_gt_dec (ea_q a + 40) (ea_v a)) as [h|h]; [left; lia|].
  destruct (Z_le_gt_dec (ea_v a + 56) (ea_q a)) as [h2|h2]; [right; lia|].
  exfalso. destruct (Hfoot (Z.max (ea_v a) (ea_q a)) ltac:(left; lia)) as (_ & Hq' & _ & _). apply Hq'. lia. }
assert (Htg6 : 0 <= PjTree.tag (ea_t a) <= 6) by (destruct (ea_t a); cbn [PjTree.tag]; lia).
remember (Eimg (Ereg regs [w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HRO : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew E n = getr regs r)
  by (intros n r Hr Hn; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (EX : forall j, (j < 4)%nat ->
          ew E (32 + j) = nth j [w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
clear HE.
assert (E2 : ew E 2 = w64 (S1a a)) by (rewrite (EW 2%nat 2%bv eq_refl ltac:(lia)); exact R2).
assert (E3 : ew E 3 = getr (ea_regs a) 3) by (rewrite (EW 3%nat 3%bv eq_refl ltac:(lia)); exact R3).
assert (E4 : ew E 4 = getr (ea_regs a) 4) by (rewrite (EW 4%nat 4%bv eq_refl ltac:(lia)); exact R4).
assert (E19 : ew E 19 = w64 (ea_q a)) by (rewrite (EW 19%nat 19%bv eq_refl ltac:(lia)); exact R19).
assert (E23 : ew E 23 = w64 (ea_v a)) by (rewrite (EW 23%nat 23%bv eq_refl ltac:(lia)); exact H23).
assert (E24 : ew E 24 = w64 SHADOW_OFF) by (rewrite (EW 24%nat 24%bv eq_refl ltac:(lia)); exact R24).
assert (E32 : ew E 32 = w64 (ea_scr a)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = w64 (ea_dl a)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = w64 (PjTree.tag (ea_t a))) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = w64 str) by exact (EX 3%nat ltac:(lia)).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = ea_v a) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF) by (rewrite E24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U34 : bv_unsigned (ew E 34) = PjTree.tag (ea_t a)) by (rewrite E34; apply unsigned_lit_small; lia).
assert (Hwr : forall o, 32 <= o < 36 -> writable_at SEGS (rdW W mem) (ea_q a + o)).
{ intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (HS : st_ok_pi SEGS VAL E ss_vn
               (restrict (w_H W) (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + (EV0 + EV_SRET))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_vn. apply pa_entry_st_ok_full.
  - apply regs_ok_pin; [exact HRO | discriminate | rewrite H10; reflexivity].
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold YP09.region_ok, vn_Rq.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [exact Hwr|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (vn_chunk_val _ _ (ea_q a) 24 8 _ (ea_scr a)); [lia| |exact Q4].
        rewrite (ev_denot_off _ 32 (ea_scr a) 0 E32 ltac:(lia) ltac:(lia)). f_equal. lia.
      * apply (vn_chunk_val _ _ (ea_q a) 32 4 _ (ea_dl a)); [lia| |exact Q5].
        rewrite (ev_denot_off _ 33 (ea_dl a) 0 E33 ltac:(lia) ltac:(lia)). f_equal. lia.
    + unfold YP09.region_ok, vn_Rv.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (vn_chunk_val _ _ (ea_v a) 0 4 _ (PjTree.tag (ea_t a))); [lia| |rewrite Z.add_0_r; exact Htgv].
        rewrite (ev_denot_off _ 34 (PjTree.tag (ea_t a)) 0 E34 ltac:(lia) ltac:(lia)). f_equal. lia.
      * apply (vn_chunk_val _ _ (ea_v a) 16 8 _ str); [lia| |exact Hstrv].
        rewrite (ev_denot_off _ 35 str 0 E35 ltac:(lia) ltac:(lia)). f_equal. lia.
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, vn_Rq, vn_Rv.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U23. repeat split; lia.
  - split.
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U19, U24, U23, U34. unfold D_QLO.
      change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
    + split; [|exact I]. cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite (ev_bne_lit _ 23%nat (ea_v a) 0 E23 ltac:(lia) ltac:(lia)).
      apply negb_true_iff, Z.eqb_neq. exact Hvn. }
assert (SHOK : sh_ok SEGS D_Bx [] E (rdW W mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUN := @paj_run_x fx' rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNTO := @paj_run_to_x fx' rc SK A_prog_listing PL PA B PST ARx hl LAWS).
pose (RUNI := @paj_run_x_inv fx' rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := @paj_run_to_x_inv fx' rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (PI := PA)).
assert (HQRA : forall m md0, ARx ly S Hp W m md0 ->
          range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (ea_q a + 24) 16).
{ intros m md0 HARm x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  apply (ZSB_x ly S Hp W m md0 x HARm). rewrite Eslo, Eshi. lia. }
assert (Ho16 : (S1a a - (sp0a a + ea_d a)) mod 16 = 0).
{ pose proof (Z.div_mod (S1a a) 32 ltac:(lia)). pose proof (Z.div_mod (sp0a a) 16 ltac:(lia)).
  pose proof (Z.div_mod (ea_d a) 16 ltac:(lia)).
  replace (S1a a - (sp0a a + ea_d a)) with ((2 * (S1a a / 32) - sp0a a / 16 - ea_d a / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
(* 0x834d4-0x834f0: a0 = 0 and v <> 0 fall through, the 4-byte check of v, v->type, the type test *)
paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan.
all: try (eapply (vn_obl _ _ _ 23 _ (ea_v a) _ (ea_v a) 56);
          [vn_ewn; exact E24 | vn_ewn; exact E23 | lia | lia | lia | lia | exact Hrav | lia | lia]).
all: try (vn_awr U19).
assert (HA1 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
          aview SEGS (w_H W) (ms_mem ms) z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnz. apply (vn_frame_aview _ _ W mem (ms_mem ms) z HFr Hz). vn_nwr U19 U23. }
psrr_branch_tok RUN BR HS SHOK D_Bspan.
- (* v->type <> PJ_STRING (0x83530-0x83550): in->differs := 1 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?EE _) _ = _ =>
    rewrite (ev_bne_lit EE 34%nat (PjTree.tag (ea_t a)) 4 ltac:(vn_ewn; exact E34) ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Htn.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_EXIT).
  all: try (eapply (vn_obl _ _ _ 19 _ (ea_q a) _ (ea_q a + 24) 16);
            [vn_ewn; exact E24 | vn_ewn; exact E19 | lia | lia | lia | lia | exact (HQRA _ _ (proj1 HJ)) | lia | lia]).
  all: try (vn_awr U19).
  assert (HA2 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
            aview SEGS (w_H W) (ms_mem ms0) z = aview SEGS (w_H W) mem z).
  { intros z Hz Hnz. rewrite <- (HA1 z Hz Hnz). apply (vn_frame_aview _ _ W (ms_mem ms) (ms_mem ms0) z HFr0 Hz).
    vn_nwr U19 U23. }
  vn_cell HS (SLit 1) HCH.
  cbn [base_val YP09.r_base] in HCH. vn_ewn_in HCH. rewrite U19 in HCH. rewrite vn_lit in HCH by lia.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (27%bv : bv 5) N27.
  pmkst HS. ev_cfg_to EV_EXIT.
  eapply (vn_exit a fx' W _ _ _ ly S Hp _ p' 1 HFX).
  + apply (ev_mid_frame B ARx SK LAWS a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ).
    * intros x Hx.
      assert (Hnw : ~ (ea_q a + 32 <= bv_unsigned x < ea_q a + 36))
        by (intros Hq; apply Hx; unfold ev_wr; right; right; exact Hq).
      rewrite (HFr0 x) by vn_nwr U19 U23. rewrite (HFr x) by vn_nwr U19 U23. reflexivity.
    * eapply ev_vm_kept; [|exact Q1]. intros kk Hk. apply mbyte_of_aview. apply HA2; lia.
    * exact HCH.
    * exact HMN.
  + apply (ev_regs_kept a regs _ HR). intros r0 Hr0. apply HK. cbv in Hr0 |- *. tauto.
  + rewrite (HK 22%bv) by (cbv; tauto). exact H22.
  + rewrite N27. reflexivity.
  + apply Hout; [right; reflexivity|].
    split; [intros _; right; split; [exact Hvn|] | intros _; reflexivity].
    intros Heq. apply Htn. rewrite Heq. reflexivity.
- (* v->type = PJ_STRING: the tree is JStr s', v->str a harness block of the ledger *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?EE _) _ = _ =>
    rewrite (ev_bne_lit EE 34%nat (PjTree.tag (ea_t a)) 4 ltac:(vn_ewn; exact E34) ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Ht4.
  assert (Hts : exists s', ea_t a = PjTree.JStr s').
  { destruct (ea_t a) as [| | | t1 c1 | s1 | l1 | m1]; cbn [PjTree.tag] in Ht4; try discriminate Ht4.
    exists s1. reflexivity. }
  destruct Hts as (s' & Ets).
  destruct (Hcs s' Ets) as (kL & (HinL & HkL & Hs32 & Hsb' & Gx) & _). unfold prh_lin in HinL.
  pose proof Hled as (_ & _ & HFL & _). rewrite Forall_forall in HFL.
  destruct (HFL _ HinL) as (HkL0 & HabL & HHpL & _). cbn [fst snd] in HkL0, HabL, HHpL.
  pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HabL) as (_ & HL4096 & HLc & _).
  pose proof (ev_req_ge (kL + cf_head)) as HLr.
  destruct Hinbs0 as (bS & mS & HinS & HbS & HbSe & HbSh).
  assert (HinS' : In (bS, mS) (ablocks B ly S)) by (rewrite Eab; exact HinS).
  pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HinS') as (_ & HS4096 & HSc & _).
  pose proof (ev_req_ge mS) as HSr.
  unfold ea_len in Hlen, Hscrc, HbSe.
  assert (Hnzx : Forall (fun c => c <> 0) s') by (eapply Forall_impl; [|exact Hsb']; intros c0 Hc0; cbv beta in *; lia).
  assert (Hnzy : Forall (fun c => c <> 0) s) by (eapply Forall_impl; [|exact Hsb]; intros c0 Hc0; cbv beta in *; lia).
  assert (HRv1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (ea_v a) 56).
  { apply (ev_ra_kept (aview SEGS (w_H W) mem)); [intros z Hz; apply HA1; lia | lia | lia | exact Hrav]. }
  (* 0x834f8-0x83528: the 8-byte checks of v + 16 and q + 24, v->str, in->scratch, `jal wrapper_strcmp` *)
  paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan.
  all: try (first
    [ eapply (vn_obl _ _ _ 23 _ (ea_v a) _ (ea_v a) 56);
        [vn_ewn; exact E24 | vn_ewn; exact E23 | lia | lia | lia | lia | exact HRv1 | lia | lia]
    | eapply (vn_obl _ _ _ 19 _ (ea_q a) _ (ea_q a + 24) 16);
        [vn_ewn; exact E24 | vn_ewn; exact E19 | lia | lia | lia | lia | exact (HQRA _ _ (proj1 HJ)) | lia | lia] ]).
  all: try (vn_awr U19).
  assert (HA2 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
            aview SEGS (w_H W) (ms_mem ms0) z = aview SEGS (w_H W) mem z).
  { intros z Hz Hnz. rewrite <- (HA1 z Hz Hnz). apply (vn_frame_aview _ _ W (ms_mem ms) (ms_mem ms0) z HFr0 Hz).
    vn_nwr U19 U23. }
  vn_cell HS (SOff 33 0) HCQ.
  cbn [base_val YP09.r_base] in HCQ. vn_ewn_in HCQ. rewrite U19 in HCQ.
  lazymatch type of HCQ with context [sv_denot ?EE (SOff 33 0)] =>
    rewrite (ev_denot_off EE 33 (ea_dl a) 0 ltac:(vn_ewn; exact E33) ltac:(lia) ltac:(lia)) in HCQ end.
  rewrite Z.add_0_r, unsigned_lit_small in HCQ by lia.
  (* the state at the call is the activation's outside in->differs: its read-only view (ev_rod) *)
  assert (HRAW : forall x : word, ~ ev_wr a (bv_unsigned x) -> mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx.
    assert (Hnw : ~ (ea_q a + 32 <= bv_unsigned x < ea_q a + 36))
      by (intros Hq; apply Hx; unfold ev_wr; right; right; exact Hq).
    rewrite (HFr0 x) by vn_nwr U19 U23. rewrite (HFr x) by vn_nwr U19 U23. reflexivity. }
  assert (Q1T : val_mem SEGS (rdW W (ms_mem ms0)) (ea_q a) 8 (ea_x0 a + p')).
  { eapply ev_vm_kept; [|exact Q1]. intros kk Hk. apply mbyte_of_aview. apply HA2; lia. }
  pose proof (ev_rod B ARx SK LAWS a ly S Hp W (ms_mem ms0) _ _ _ _ _ HP
    (ev_mid_frame B ARx SK LAWS a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ HRAW Q1T HCQ HMN)) as HRODT.
  first [ pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS
            ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK
        | pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS
            ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK ].
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) Pa0. prreg HS (11%bv : bv 5) Pa1. prreg HS (1%bv : bv 5) Pra.
  assert (HspT : spZ (ms_regs ms0) = S1a a).
  { unfold spZ. rewrite (HK 2%bv) by (cbv; tauto). rewrite R2. apply unsigned_lit_small. lia. }
  assert (GxT : garr8 SEGS (rdW W (ms_mem ms0)) str (s' ++ [0])).
  { eapply ev_garr8_kept; [|exact Gx]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    apply mbyte_of_aview. apply HA2; lia. }
  assert (GyT : garr8 SEGS (rdW W (ms_mem ms0)) (ea_scr a) (s ++ [0])).
  { eapply ev_garr8_kept; [|exact Hby]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    apply mbyte_of_aview. apply HA2; lia. }
  pmkst HS.
  eapply SRr_bind.
  { eapply (YGcallMxmn.aj_strcmp_at_xrom (fx := fx') (SK := SK) SEGS B PST ARx
      (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) LAWS (@pa_segs_low _ A_prog_listing PA)
      (SIGMA AS___wrap_strcmp) (SCMP fx') W (ms_regs ms0) (ms_mem ms0)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str (ea_scr a)
      (Z.of_nat (length s')) (Z.of_nat (length s))
      (S1a a - (sp0a a + ea_d a)) _ HJ).
    - rewrite Pa0, E35. reflexivity.
    - rewrite Pa1, E32. reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite HspT. lia.
    - exact Ho16.
    - lia.
    - unfold ESTACK. rewrite EK. lia.
    - rewrite (HK 3%bv) by (cbv; tauto). rewrite R3. exact Hgp0.
    - rewrite (HK 4%bv) by (cbv; tauto). rewrite R4. exact Htp0.
    - exact Pra.
    - apply (ret_ok_codeptr_v (PI := PA)); [split; apply Z.leb_le || apply Z.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity].
    - exact (vn_first_byte W (ms_mem ms0) str s' GxT Hnzx).
    - exact (vn_first_byte W (ms_mem ms0) (ea_scr a) s GyT Hnzy).
    - replace (Z.of_nat (length s') + 1) with (Z.of_nat (length (s' ++ [0]))) by (rewrite length_app; cbn [length]; lia).
      apply (vn_src_ok W (ms_regs ms0) (ms_mem ms0) str _ GxT).
      intros a0 Ha0. rewrite length_app in Ha0. cbn [length] in Ha0. rewrite HspT. unfold ESTACK. lia.
    - replace (Z.of_nat (length s) + 1) with (Z.of_nat (length (s ++ [0]))) by (rewrite length_app; cbn [length]; lia).
      apply (vn_src_ok W (ms_regs ms0) (ms_mem ms0) (ea_scr a) _ GyT).
      intros a0 Ha0. rewrite length_app in Ha0. cbn [length] in Ha0. rewrite HspT. unfold ESTACK. lia.
    - intros a0 Ha0. unfold ESTACK. lia.
    - intros a0 Ha0. unfold ESTACK. lia.
    - exact (vn_am8 ly S Hp W mem md _ _ str (Z.of_nat (length s')) HAR HabL ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (vn_am8 ly S Hp W mem md _ _ (ea_scr a) (Z.of_nat (length s)) HAR HinS' ltac:(lia) ltac:(lia) ltac:(lia)).
    - refine (proj1 (ev_blk_shadow B ARx HSHD ly S Hp W (ms_mem ms0) _ _ _ str _ (proj1 HJ) HabL _ _ _));
        first [apply ev_hd_le; [lia | intros _; lia] | lia].
    - refine (proj2 (ev_blk_shadow B ARx HSHD ly S Hp W (ms_mem ms0) _ _ _ str _ (proj1 HJ) HabL _ _ _) _);
        first [apply ev_hd_le; [lia | intros _; lia] | lia].
    - (* the scratch's shadow: MID's wdest_ok, kept by the view below alloc_ceiling *)
      apply (range_addressable_sub _ _ (ea_scr a) (Z.of_nat (length (ea_x a)) + 1)); [| lia | lia].
      apply (ev_ra_kept (aview SEGS (w_H W) mem)); [intros z Hz; apply HA2; lia | lia | lia | exact HWra].
    - apply (ev_hull_sub _ (ea_scr a) (Z.of_nat (length (ea_x a)) + 1)); [| lia | lia | lia].
      apply (ev_hull_kept (aview SEGS (w_H W) mem)); [intros z Hz; apply HA2; lia | lia | lia | lia |
        exact (HWhv ltac:(unfold ea_len; lia))].
    - apply (vn_tail ly S Hp W (ms_mem ms0) _ _ _ str (Z.of_nat (length s')) (proj1 HJ) HabL); lia.
    - apply (vn_tail ly S Hp W (ms_mem ms0) _ _ _ (ea_scr a) (Z.of_nat (length s)) (proj1 HJ) HinS'); lia.
    - (* the read-only premise: the walk's own state at the call (ev_rod), no image fact *)
      exact HRODT. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & rv & -> & HJ2 & HP2 & Hres & Hcmp & Hfr2 & Hpres2 & HMNk2).
  pose proof (HMNk2 HMN) as HMN2. clear HMN HMNk2. rename HMN2 into HMN.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2J & _).
  assert (Hcmp' : rv = w64 0 <-> s' = s).
  { rewrite Hcmp. exact (vn_str_eq (w_H W) (ms_mem ms0) str (ea_scr a) s' s GxT GyT). }
  assert (HA3 : forall z, 0 <= z < 2 ^ 64 -> ~ (S1a a - 8192 <= z < S1a a) -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
            aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) mem z).
  { intros z Hz Hw Hq. rewrite (Hfr2 z Hz ltac:(unfold ESTACK; lia)). apply HA2; assumption. }
  (* back at 0x8352c (`beqz a0, 0x83cb0`): the regions at in and at v are kept (strcmp writes only its window) *)
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1]%nat HSX.
  lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
  { constructor; [|constructor; [|apply Forall_nil]]; split.
    - intros z Hz. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hz. vn_ewn_in Hz. rewrite U19 in Hz.
      apply mbyte_of_aview. apply Hfr2; [lia | unfold ESTACK; lia].
    - intros z Hz _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz. vn_ewn_in Hz. rewrite U19 in Hz.
      apply (apresent_writable SEGS). apply Hpres2J. lia.
    - intros z Hz. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hz. vn_ewn_in Hz. rewrite U23 in Hz.
      destruct (Hfoot z ltac:(left; lia)) as (_ & _ & Hns & _). change (spZ (ea_regs a)) with (sp0a a) in Hns.
      apply mbyte_of_aview. apply Hfr2; [lia | unfold ESTACK; lia].
    - intros z Hz. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz. exfalso. lia. }
  specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
  lazymatch type of HSX with st_ok_pi _ _ ?E1 _ _ =>
    assert (HEIs : img_env VAL A_LIM E1) by (apply img_env_havoc; [assumption | cbv; lia]);
    assert (Ea0 : ew E1 52 = rv) by (rewrite <- Hres; reflexivity);
    assert (SHOK1 : sh_ok SEGS D_Bx [] E1 (rdW W mem2)) by apply Forall_nil end.
  clear HS HJ SHOK. rename HSX into HS. rename HJ2 into HJ. rename SHOK1 into SHOK.
  psrr_branch_tok RUN BR HS SHOK D_Bspan.
  + (* strcmp = 0 (0x83cb0): the strings are equal, in->differs kept *)
    pose proof (vn_br_eq_t _ 52 rv Ea0 Hc) as Hrv0.
    pose proof (proj1 Hcmp' Hrv0) as Heqs.
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_EXIT).
    all: try (vn_awr U19).
    vn_cell HS (SOff 33 0) HCH.
    cbn [base_val YP09.r_base] in HCH. vn_ewn_in HCH. rewrite U19 in HCH.
    lazymatch type of HCH with context [sv_denot ?EE (SOff 33 0)] =>
      rewrite (ev_denot_off EE 33 (ea_dl a) 0 ltac:(vn_ewn; exact E33) ltac:(lia) ltac:(lia)) in HCH end.
    rewrite Z.add_0_r, unsigned_lit_small in HCH by lia.
    assert (HAF : forall z, 0 <= z < 2 ^ 64 -> ~ (S1a a - 8192 <= z < S1a a) -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
              aview SEGS (w_H W) (ms_mem ms1) z = aview SEGS (w_H W) mem z).
    { intros z Hz Hw Hq. rewrite <- (HA3 z Hz Hw Hq). apply (vn_frame_aview _ _ W mem2 (ms_mem ms1) z HFr1 Hz).
      vn_nwr U19 U23. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    prreg HS (27%bv : bv 5) N27.
    pmkst HS. ev_cfg_to EV_EXIT.
    eapply (vn_exit a fx' W _ _ _ ly S Hp _ p' (ea_dl a) HFX).
    * apply (ev_mid_av a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ).
      -- intros z Hz Hw. apply HAF; [exact Hz | intros Hc'; apply Hw; unfold ev_wr; left; lia |
           intros Hc'; apply Hw; unfold ev_wr; right; right; exact Hc'].
      -- eapply ev_vm_kept; [|exact Q1]. intros kk Hk. apply mbyte_of_aview. apply HAF; lia.
      -- exact HCH.
      -- exact HMN.
    * apply (ev_regs_kept a regs _ HR). intros r0 Hr0. apply HK2. cbv in Hr0 |- *. tauto.
    * rewrite (HK2 22%bv) by (cbv; tauto). exact H22.
    * rewrite N27. reflexivity.
    * apply Hout; [exact Hdl|]. split; [intros H1; left; exact H1|].
      intros [H1|(_ & Hne)]; [exact H1|]. exfalso. apply Hne. rewrite Ets, Heqs. reflexivity.
  + (* strcmp <> 0 (0x83530-0x83550): the strings differ, in->differs := 1 *)
    pose proof (vn_br_eq_f _ 52 rv Ea0 Hc) as Hrv0.
    assert (Hne : s' <> s) by (intro Heq; apply Hrv0; apply Hcmp'; exact Heq).
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_EXIT).
    all: try (eapply (vn_obl _ _ _ 19 _ (ea_q a) _ (ea_q a + 24) 16);
              [vn_ewn; exact E24 | vn_ewn; exact E19 | lia | lia | lia | lia | exact (HQRA _ _ (proj1 HJ)) | lia | lia]).
    all: try (vn_awr U19).
    vn_cell HS (SLit 1) HCH.
    cbn [base_val YP09.r_base] in HCH. vn_ewn_in HCH. rewrite U19 in HCH. rewrite vn_lit in HCH by lia.
    assert (HAF : forall z, 0 <= z < 2 ^ 64 -> ~ (S1a a - 8192 <= z < S1a a) -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
              aview SEGS (w_H W) (ms_mem ms1) z = aview SEGS (w_H W) mem z).
    { intros z Hz Hw Hq. rewrite <- (HA3 z Hz Hw Hq). apply (vn_frame_aview _ _ W mem2 (ms_mem ms1) z HFr1 Hz).
      vn_nwr U19 U23. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK2.
    cbn [ms_regs restrict] in HK2.
    prreg HS (27%bv : bv 5) N27.
    pmkst HS. ev_cfg_to EV_EXIT.
    eapply (vn_exit a fx' W _ _ _ ly S Hp _ p' 1 HFX).
    * apply (ev_mid_av a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ).
      -- intros z Hz Hw. apply HAF; [exact Hz | intros Hc'; apply Hw; unfold ev_wr; left; lia |
           intros Hc'; apply Hw; unfold ev_wr; right; right; exact Hc'].
      -- eapply ev_vm_kept; [|exact Q1]. intros kk Hk. apply mbyte_of_aview. apply HAF; lia.
      -- exact HCH.
      -- exact HMN.
    * apply (ev_regs_kept a regs _ HR). intros r0 Hr0. apply HK2. cbv in Hr0 |- *. tauto.
    * rewrite (HK2 22%bv) by (cbv; tauto). exact H22.
    * rewrite N27. reflexivity.
    * apply Hout; [right; reflexivity|].
      split; [intros _; right; split; [exact Hvn|] | intros _; reflexivity].
      rewrite Ets. intros Heq. injection Heq as Heq. exact (Hne Heq).
Qed.

(* ---- PIECE 3 from the call, the two short exits and the v <> 0 tail ---- *)
Lemma ev_string_of_vn : ev_str_vn_stmt ->
  ev_string_spec (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
intros VN a fxc W regs mem md ly S Hp k i1 c HP HFX HK Ec. subst c.
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsrc0 & _).
pose proof Hsrc0 as (Hg0 & _).
eapply SRr_bind; [exact (ev_str_call a fxc W regs mem md ly S Hp k i1 HP HFX HK)|].
cbv beta. intros W' c' _ (fx' & regs' & mem' & md' & ly' & S' & Hp' & k' & -> & HFX' & Hsret).
destruct Hsret as (HR & H22 & H23 & H27 & Hi & Hc & Hsk & Hcase).
destruct (fst (fst (PjGrammar.jr_string (skipn (Nat.succ i1) (ea_x a)) []))) as [[s rest]|] eqn:Ejr.
- destruct Hcase as (Ha0 & (cc & Hsc & Hrest & HM') & Hby).
  destruct (ex_string_rest _ _ _ Ejr) as (c0 & Hsc0 & Hrest0 & Hclt & Hsl & Hbytes).
  rewrite Hsc in Hsc0. injection Hsc0 as <-.
  rewrite length_skipn in Hclt. unfold Nat.succ in Hclt.
  assert (Epp : ea_x0 a + Z.of_nat i1 + Z.of_nat cc + 2 = ea_x0 a + (Z.of_nat i1 + Z.of_nat cc + 2)) by lia.
  rewrite Epp in HM'.
  assert (Hout : forall dl', (dl' = 0 \/ dl' = 1) ->
            (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> PjTree.JStr s)) ->
            ev_out (L := A_prog_listing) (PA := PA) a 0 (Z.of_nat i1 + Z.of_nat cc + 2) (ea_dep a) dl').
  { intros dl' H01 Hiff. apply (ev_string_out a i1 0 _ dl' Hi Hc Hsk Hdl ltac:(lia)). rewrite Ejr.
    split; [reflexivity|]. split; [rewrite Hrest, !length_skipn; unfold Nat.succ; clear - Hclt; lia|]. split; [exact H01 | exact Hiff]. }
  destruct (Z.eq_dec (ea_v a) 0) as [Hv0|Hvn].
  + apply (ev_str_v0 a fx' W' regs' mem' md' ly' S' Hp' k' _ HP HFX' HM' HR H22 Ha0 ltac:(rewrite H23, Hv0; reflexivity)).
    apply Hout; [exact Hdl|]. split; [intros H; left; exact H | intros [H|(Hv & _)]; [exact H | contradiction]].
  + apply (VN a fx' W' regs' mem' md' ly' S' Hp' k' _ s HP HFX' HM' HR H22 Ha0 H23 Hvn Hby); [| lia | exact Hout].
    apply Hbytes. rewrite Forall_forall. intros b Hb. apply In_nth with (d := 0) in Hb as (j & Hj & <-).
    rewrite length_skipn in Hj. rewrite nth_skipn.
    exact (proj2 (Hg0 (Nat.succ i1 + j)%nat ltac:(lia))).
- destruct Hcase as (Ha0 & HM').
  apply (ev_str_none a fx' W' regs' mem' md' ly' S' Hp' k' i1 HP HFX' HM' HR H22 H27 Ha0).
  apply (ev_string_out a i1 (-1) _ (ea_dl a) Hi Hc Hsk Hdl ltac:(lia)). rewrite Ejr.
  split; [reflexivity|]. split; reflexivity.
Qed.

(* ======== ev_disp: pieces 2 + 3 + 4 (S8aIface.ev_disp_spec) from S8aDisp's d_ws and the two leaves ======== *)
Lemma ev_disp_of :
  ev_string_spec (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK ->
  ev_word_spec (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK ->
  ev_disp_spec (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
intros HSTR HWD a fxc W regs mem md ly S Hp k HP HFX HWS.
eapply SRr_bind; [exact (d_ws B ARx SK LAWS ZSB_x a fxc W regs mem md ly S Hp k HP HFX HWS)|].
cbv beta. intros W' c' _ [Hex | (fx' & regs' & mem' & md' & ly' & S' & Hp' & k' & i1 & c & off & HFX' & -> & HK & Hkc)].
- apply SRr_ret. left. exact Hex.
- unfold ev_kind_pc in Hkc.
  destruct Hkc as [(-> & ->) | [(-> & ->) | [(-> & ->) | [(-> & ->) | [(Hc & ->) | (H1 & H2 & H3 & H4 & H5 & H6 & ->)]]]]].
  + eapply SRr_mono; [exact (HSTR a fx' W' regs' mem' md' ly' S' Hp' k' i1 34 HP HFX' HK eq_refl)|].
    intros W'' c'' _ H. left. exact H.
  + eapply SRr_mono; [exact (HWD a fx' W' regs' mem' md' ly' S' Hp' k' i1 102 EV_WORD_F HP HFX' HK
      ltac:(left; split; reflexivity))|].
    intros W'' c'' _ H. left. exact H.
  + eapply SRr_mono; [exact (HWD a fx' W' regs' mem' md' ly' S' Hp' k' i1 110 EV_WORD_N HP HFX' HK
      ltac:(right; left; split; reflexivity))|].
    intros W'' c'' _ H. left. exact H.
  + eapply SRr_mono; [exact (HWD a fx' W' regs' mem' md' ly' S' Hp' k' i1 116 EV_WORD_T HP HFX' HK
      ltac:(right; right; split; reflexivity))|].
    intros W'' c'' _ H. left. exact H.
  + apply SRr_ret. right. exists fx', regs', mem', md', ly', S', Hp', k', i1, c.
    split; [exact HFX'|]. split; [exact HK|]. left. split; [exact Hc | reflexivity].
  + apply SRr_ret. right. exists fx', regs', mem', md', ly', S', Hp', k', i1, c.
    split; [exact HFX'|]. split; [exact HK|]. right. repeat split; assumption.
Qed.

(* ======== PIECE 3 CLOSED ======== *)
Lemma ev_string : ev_string_spec (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (ev_string_of_vn ev_str_vn). Qed.

(* S8aWord.v's WORDX and TS (ev_word's), verbatim. STAND-IN: the ex_word walk (the text tex_word_specX, PRH_FnEx.v;
   owner the unit owner's S8b), at every float state (ex_word touches none; the unit owner ruled the forall fx1 form).
   The text carries `0 <= v /\ v + 4 <= 2 ^ 47` since the kit merged here; ev_word discharges it at its call. *)
Hypothesis WORDX : forall fx1, tex_word_specX (fx := fx1) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
(* OWNER the final image instance (AD2l.v TfibB_syms, Qed): image A's symbol record, S8aEntry.v's TS. ev_word reads
   the literals' tables from it (S8aWord.ev_lit_img); the stand-in LIT is DELETED (S8aWord.ev_lit_cstr). *)
Hypothesis TS : AF0m.TfibSyms B.

(* ======== PIECES 2 + 3 + 4 CLOSED ======== *)
Lemma ev_disp : ev_disp_spec (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (ev_disp_of ev_string (ev_word B ARx SK LAWS HSHD WORDX TS)). Qed.
End w.
