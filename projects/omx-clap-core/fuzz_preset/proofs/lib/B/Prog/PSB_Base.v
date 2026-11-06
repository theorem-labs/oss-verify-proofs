(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 635 of its 665 lines of code are new or changed and 322 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsRet.v, with its module paths and module names changed; 354 of its 408 lines of code are new or changed and 611 lines of the source are left out. *)
(* fuzz_preset lib/B, parse_string on image B (asan-ubsan, B_entry slot of a Theorem Labs lane's whole-program listing
   lib/B/Listing_prog.v + PAImg_prog.v, 386 instructions): the walk's B CUT LAYER.
   rule 24: proves no function (kind: statement text). The function proof is parse_string_holds_B (PSB_Top.v); its reuse search
   is in that file's header.
   The goal is the kit's tparse_string_specX (lib/A/PRH_FnReader.v blob f1ae32e3b2cd at the kit's cut 7cdbb61b5fa0) at image B's
   instances (prh_img_B, B_prog_listing, PI_prog_B). The image-free part of the cut layer (the entry record, the
   premises, the post ps_post, the carried journal ps_carry, ps_dec_rel, ps_alloc, ps_at_ret0, ps_close,
   ps_holds_of_entry) is lib/A/Prog/PS_Gen.v, shared with image A's walk (WalkS4); this file adds B's register maps,
   B's cut offsets and the B stretch statements. FILE SET: every non-lane file as the kit's cut carries it (YCbqG.v
   219748197d6b, B Listing_prog.v c97cc46b3e13, PRW_StepKit.v 0df3991c13f4 / PRW_HShadow.v 2662d68ca36b); earlier the kit
   PREVIEW walkkit-next 0afb3f76c28, engine and YCbqG.v from a working branch 63997a07aa6, listing a working branch 7c8ffeba5035.
   THE CUTS (DERIVED byte offsets from parse_string's B entry, read off the neutral listing of the rebuilt image B,
   asan-ubsan sha256 f8f98a95bc52 (the internal file neutral_dis.py omx-clap-core-preset-ranout/asan-ubsan/fuzz_preset),
   the neutral listing parse_string.fuzz_preset.asan-ubsan.s (sha256 549ddc2d23bf; internal record)):
     0     entry   prologue (13 saves, frame 144), s0 = q, the q alignment check, the GOT load of the
                   shadow base (s7), the shadow checks of q (s6) and q + 8 (s8), s4 = p + 1, its wrap check,
                   a1 = end; p + 1 >= end goes to RET0
     148   SCAN    the scan loop head (`srli a3, a0, 3`): a0 = the cursor, a1 = end, a2 = 34; the closing quote
                   goes to the length (216) and `jal fuzz_malloc` (224), NULL to RET0; then s2 = out, the q + 8
                   shadow re-check, s3 = s2 and the constants block
     324   DEC     the decode loop head (`srli a1, s4, 3`): s4 = r, s3 = w, s2 = out, a0 = end
     436   U       the \u escape (`sub a0, a0, s5` after the 'u' compare): s5 = r + 2; hex4 at 456, the surrogate
                   pair (a second hex4 at 968), put_utf8 at 1040, back to the loop tail
     1248  FREE    `mv a0, s2` before `jal fuzz_free` (1252): every bad escape
     1256  RET0    `li s2, 0`, the join of every refusing path; 1260 `mv a0, s2` and the epilogue
     1324  RETOK   the closing quote in decode: the NUL store's shadow check, the NUL at w, the q shadow re-check,
                   in->p = r + 1, `j` to the epilogue
   Every UBSan check of B (21, the internal file B-U-TRAPS.md:196-216) branches to `unimp` at 1372; each is NOT TAKEN under the
   premises; every ASan check branches to an errpath_* report call; each is NOT TAKEN (the shadow is 0 there).
   Numerals: the offsets above (DERIVED: byte offsets inside parse_string), register numbers (WORD), the decode
   constants 34 / 32 / 92 / -1 / 101 / 91 / 113 / 114 / 117 and the three surrogate words 55296 / 56320 /
   -56613888 (WORD: characters, the listing's li / lui immediates), 4 / 8 / 24 / 136 / 144 (LENGTH). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* srr_inv_laws lives in YC80x since the s1b collapse (preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record)); YSRrMemnorm keeps the lemmas *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PS_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
(* the re-hiding move's SRr' / SRrG / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section psb. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* image B's instances, bound ONCE here and passed explicitly everywhere below; the sink SK is an explicit Variable *)
#[local] Instance PSB_PrhImg : PrhImg := prh_img_B.
#[local] Instance PSB_PAListing : PAListing B_prog_listing := PL_prog_B.
#[local] Instance PSB_PAImg : PAImg B_prog_listing := PI_prog_B.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PSB_PAImg).
#[local] Notation BASE := (@pa_val _ B_prog_listing PSB_PAImg A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the run's caller contexts and the cursor set CW (the kit cut 7cdbb61b5fa0: the closure takes no run words; the cursor
   free's trace is in CW, PRH_Base.prh_cw_ok) *)
Variable CTX : list (list Z).
Variable CW : list (list Z).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation LEDGER := (prh_ledger B).
#[local] Notation ps_in := (ps_in (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_SP := (PS_SP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_carry := (ps_carry (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_alloc := (ps_alloc (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_pre := (ps_pre (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx).
#[local] Notation ps_post := (ps_post (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK CW).
#[local] Notation ps_at_ret0 :=
  (ps_at_ret0 (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK CW).
(* the post and the NULL return's cut over a world relation R (PS_Gen's R forms beside) *)
#[local] Notation ps_postR := (ps_postR (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_at_ret0R :=
  (ps_at_ret0R (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).

(* ---- B's cut offsets: DERIVED byte offsets inside parse_string (header) ---- *)
Definition PSB_SLOT : nat := B_prog_slot AS_parse_string.
Definition PSB_OFF : Z := 4 * Z.of_nat PSB_SLOT.
Lemma PSB_entry_sigma : SIGMA AS_parse_string = BASE + PSB_OFF.
Proof. vm_compute. reflexivity. Qed.
Definition PSB_SCAN : Z := 148.
Definition PSB_DEC : Z := 324.
Definition PSB_U : Z := 436.
Definition PSB_FREE : Z := 1248.
Definition PSB_RET0 : Z := 1256.
Definition PSB_RETOK : Z := 1324.
Definition psb_pc (off : Z) : Z := BASE + PSB_OFF + off.
(* the cursor store `sd s4, 0(s0)` (B 0x88650), parse_string's ONLY write at or above its entry sp (the caller's word
   in->p, FP), on the success tail after every call: DERIVED offset PSB_RETOK + 40 *)
Definition PSB_CURSOR_STORE : Z := 1364.
(* parse_string's allocator calls run with s0 = q on image B (pi_s0cur F_parse_string = Some 0: `addi s0, a0, 0` at
   B 0x88134, PRH_ImgB's evidence), so ps_chain_call's gap premise is the kit's spZ regs + 16 <= q *)
Lemma psb_s0_q : forall q, prh_s0 (PI := PSB_PrhImg) F_parse_string q = q.
Proof. intros q. cbv [prh_s0 pi_s0cur PSB_PrhImg prh_img_B]. lia. Qed.

(* ---- the three shadow registers the prologue sets and the body keeps (B offsets 76-120): s7 (x23) the shadow base,
   s6 (x22) the shadow CELL of q, s8 (x24) the shadow cell of q + 8 ---- *)
Definition psb_sh_regs (D : ps_in) (regs : bvmap 5 word) : Prop :=
  getr regs 23 = w64 SHADOW_OFF /\
  getr regs 22 = w64 (SHADOW_OFF + pi_q D / 8) /\
  getr regs 24 = w64 (SHADOW_OFF + (pi_q D + 8) / 8).

(* ---- the scan loop head (SCAN): a0 = x the cursor, a1 = end, a2 = 34, s4 = p + 1, s0 = q, s1 = q + 8; the scan
   from p + 1 is the scan from x shifted by the bytes passed (WalkS4's ps_at_scan, B's registers) ---- *)
Definition psb_at_scan (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
  ps_carry D ly S Hp W mem md 0 [] /\ psb_sh_regs D regs /\ ps_gptp D regs /\
  ly = pi_ly D /\ S = pi_S D /\ Hp = pi_Hp D /\ W = pi_W D /\
  LEDGER ly S Hp W mem (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 10 = w64 x /\
  getr regs 11 = w64 (pi_text D + pi_len D) /\ getr regs 12 = w64 34 /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\ getr regs 20 = w64 (pi_p D + 1) /\
  pi_p D + 1 <= x < pi_text D + pi_len D /\
  PjGrammar.scan (ps_x D) =
    option_map (fun Q => (Q + Z.to_nat (x - (pi_p D + 1)))%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) x)).

(* ---- the decode loop's constant registers (B offsets 252-312) and the three surrogate words on the frame: s9 34,
   s10 -1, s11 92, a4 32, a5 101, a6 91, a7 113, t0 114; sp + 24 = 55296 (0xD800), sp + 16 = 56320 (0xDC00), sp + 8
   = -56613888 (PjGrammar.pair_cp's additive constant 65536 - 55296 * 1024 - 56320). put_utf8 clobbers a4 .. t0 and the
   code reloads them at 1044-1060; s9 .. s11 are callee-saved ---- *)
Definition psb_dec_consts (D : ps_in) (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word) : Prop :=
  getr regs 25 = w64 34 /\ getr regs 26 = w64 (-1) /\ getr regs 27 = w64 92 /\
  getr regs 14 = w64 32 /\ getr regs 15 = w64 101 /\ getr regs 16 = w64 91 /\ getr regs 17 = w64 113 /\
  getr regs 5 = w64 114 /\
  val_mem segs (rdW W mem) (PS_SP D + 24) 8%nat 55296 /\
  val_mem segs (rdW W mem) (PS_SP D + 16) 8%nat 56320 /\
  val_mem segs (rdW W mem) (PS_SP D + 8) 8%nat (-56613888).

(* ---- the decode loop head (DEC): s4 = r, s3 = w, s2 = out, a0 = end (WalkS4's ps_at_dec, B's registers) ---- *)
Definition psb_at_dec (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carry D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ psb_sh_regs D regs /\
  ps_gptp D regs /\ psb_dec_consts D W mem regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 10 = w64 (pi_text D + pi_len D) /\ getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  ps_dec_rel D W mem out w r Q.

(* ---- the \u escape (U): the decode head's facts at r (the backslash), s5 = r + 2, a0 = end, and the two bytes
   read: text[r] = '\\', text[r + 1] = 'u' ---- *)
Definition psb_at_u (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carry D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ psb_sh_regs D regs /\
  ps_gptp D regs /\ psb_dec_consts D W mem regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 21 = w64 (r + 2) /\
  getr regs 10 = w64 (pi_text D + pi_len D) /\ getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  nth_error (pi_tb D) (Z.to_nat (r - pi_text D)) = Some 92 /\
  nth_error (pi_tb D) (Z.to_nat (r + 1 - pi_text D)) = Some 117 /\
  ps_dec_rel D W mem out w r Q.

(* ---- a bad escape (FREE): out is the new block, decode refuses the text; s2 = out, s0 = q (the free's trace reads
   the chain from q) ---- *)
Definition psb_at_free (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out : Z) (Q : nat) : Prop :=
  (exists k, ps_carry D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\ PjGrammar.decode (ps_x D) = None /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 8 = w64 (pi_q D).

(* ---- the success tail (RETOK): s3 = w, s4 = r at the closing quote, s2 = out, s0 = q, s6 its shadow cell
   (WalkS4's ps_at_retok, B's registers) ---- *)
Definition psb_at_retok (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carry D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ psb_sh_regs D regs /\
  ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  r = pi_p D + 1 + Z.of_nat Q /\
  (exists s, PjGrammar.decode (ps_x D) = Some (s, rest_atR (pi_tb D) (pi_text D) (r + 1)) /\
     bytes_at W mem out s /\ Z.of_nat (length s) = w - out) /\
  out <= w /\ w - out <= Z.of_nat Q.

(* ---- the stretch statements. Each ends in the text's post (at the Section's cursor set CW: the batch text's
   budgeted post), so they compose by `apply`. The decode loop is one induction on the bytes left before the closing
   quote (Q - (r - (p + 1))); the \u stretch takes the loop's hypothesis below its own measure. A stretch whose run may
   reach the bad escape's fuzz_free (entry, scan, the loop, \u, free) concludes SRr' segs RZ_cf with ps_postR at
   wle' segs RZ_cf; retok ends at wle; ret0 is reached on both sides of the free, so it has its form over R beside
   (psb_seg_ret0R; psb_seg_ret0 is its instance at wle). ---- *)
Definition psb_seg_entry : Prop :=
  forall D, ps_pre CTX CW D ->
  SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (SIGMA AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_scan : Prop :=
  forall D ly S Hp W regs mem md x, ps_pre CTX CW D -> psb_at_scan D ly S Hp W regs mem md x ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_SCAN) regs mem md)
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_dec_lt (m : nat) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_dec D ly S Hp W regs mem md out w r Q ->
  (Q - Z.to_nat (r - (pi_p D + 1)) < m)%nat ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_DEC) regs mem md)
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_dec : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_dec D ly S Hp W regs mem md out w r Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_DEC) regs mem md)
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_u : Prop :=
  forall m, psb_dec_lt m ->
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_u D ly S Hp W regs mem md out w r Q ->
  (Q - Z.to_nat (r - (pi_p D + 1)) <= m)%nat ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_U) regs mem md)
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_free : Prop :=
  forall D ly S Hp W regs mem md out Q, ps_pre CTX CW D -> psb_at_free D ly S Hp W regs mem md out Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_FREE) regs mem md)
    (ps_postR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_ret0 : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0 D ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (psb_pc PSB_RET0) regs mem md) (ps_post D).
Definition psb_seg_ret0R (R : world segs -> world segs -> Prop) : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0R R CW D ly S Hp W regs mem md ->
  SRrG segs R W (cfg_at segs (psb_pc PSB_RET0) regs mem md) (ps_postR R CW D).
Lemma psb_seg_ret0_R_wle : psb_seg_ret0 = psb_seg_ret0R (@wle segs).
Proof. reflexivity. Qed.
Definition psb_seg_retok : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_retok D ly S Hp W regs mem md out w r Q ->
  SRr segs W (cfg_at segs (psb_pc PSB_RETOK) regs mem md) (ps_post D).

(* the decode loop from its \u stretch and the loop body at one measure (the loop body's statement takes the loop
   below the current measure, as psb_seg_u does) *)
Definition psb_dec_step : Prop :=
  forall m, psb_dec_lt m -> psb_dec_lt (S m).
Lemma psb_seg_dec_of_step : psb_dec_step -> psb_seg_dec.
Proof.
intros HST.
assert (ALL : forall m, psb_dec_lt m).
{ induction m as [|m IH].
  - intros D ly S Hp W regs mem md out w r Q _ _ H. exfalso. lia.
  - exact (HST m IH). }
intros D ly S Hp W regs mem md out w r Q HP HA.
apply (ALL (Nat.succ (Q - Z.to_nat (r - (pi_p D + 1)))) D ly S Hp W regs mem md out w r Q HP HA).
apply Nat.lt_succ_diag_r.
Qed.



(* ==== THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z; the B twin of WalkS4's S4_PsBase.v gp section, 44a91d58bb5):
   every cut and stretch statement over an invariant P of the memory, carried as ps_carryP's last conjunct and at the
   post (ps_postP). The definitions above stay byte-identical; they are the P := (fun _ => True) instances
   (psb_seg_*_of_True). The top instantiates P once per record as PS_Gen's ps_mn D. ==== *)
Section gp.
Variable P : (word -> option byte) -> Prop.
#[local] Notation ps_carryP := (ps_carryP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).
#[local] Notation ps_postP := (ps_postP (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P CW).
#[local] Notation ps_at_ret0P :=
  (ps_at_ret0P (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P CW).
#[local] Notation ps_postPR :=
  (ps_postPR (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).
#[local] Notation ps_at_ret0PR :=
  (ps_at_ret0PR (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).
Definition psb_at_scanP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
  ps_carryP D ly S Hp W mem md 0 [] /\ psb_sh_regs D regs /\ ps_gptp D regs /\
  ly = pi_ly D /\ S = pi_S D /\ Hp = pi_Hp D /\ W = pi_W D /\
  LEDGER ly S Hp W mem (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 10 = w64 x /\
  getr regs 11 = w64 (pi_text D + pi_len D) /\ getr regs 12 = w64 34 /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\ getr regs 20 = w64 (pi_p D + 1) /\
  pi_p D + 1 <= x < pi_text D + pi_len D /\
  PjGrammar.scan (ps_x D) =
    option_map (fun Q => (Q + Z.to_nat (x - (pi_p D + 1)))%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) x)).
Definition psb_at_decP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carryP D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ psb_sh_regs D regs /\
  ps_gptp D regs /\ psb_dec_consts D W mem regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 10 = w64 (pi_text D + pi_len D) /\ getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  ps_dec_rel D W mem out w r Q.
Definition psb_at_uP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carryP D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ psb_sh_regs D regs /\
  ps_gptp D regs /\ psb_dec_consts D W mem regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 21 = w64 (r + 2) /\
  getr regs 10 = w64 (pi_text D + pi_len D) /\ getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  nth_error (pi_tb D) (Z.to_nat (r - pi_text D)) = Some 92 /\
  nth_error (pi_tb D) (Z.to_nat (r + 1 - pi_text D)) = Some 117 /\
  ps_dec_rel D W mem out w r Q.
Definition psb_at_freeP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out : Z) (Q : nat) : Prop :=
  (exists k, ps_carryP D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  PjGrammar.scan (ps_x D) = Some Q /\ PjGrammar.decode (ps_x D) = None /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 8 = w64 (pi_q D).
Definition psb_at_retokP (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  (exists k, ps_carryP D ly S Hp W mem md k []) /\ ps_alloc D ly S Hp W mem out Q /\ psb_sh_regs D regs /\
  ps_gptp D regs /\
  pj_in_okR segs (rdW W mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  PjGrammar.scan (ps_x D) = Some Q /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  r = pi_p D + 1 + Z.of_nat Q /\
  (exists s, PjGrammar.decode (ps_x D) = Some (s, rest_atR (pi_tb D) (pi_text D) (r + 1)) /\
     bytes_at W mem out s /\ Z.of_nat (length s) = w - out) /\
  out <= w /\ w - out <= Z.of_nat Q.
Definition psb_seg_entryP : Prop :=
  forall D, ps_pre CTX CW D -> P (pi_mem D) ->
  SRr' segs YGcfRehidePost.RZ_cf (pi_W D) (cfg_at segs (SIGMA AS_parse_string) (pi_regs D) (pi_mem D) (pi_md D))
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_scanP : Prop :=
  forall D ly S Hp W regs mem md x, ps_pre CTX CW D -> psb_at_scanP D ly S Hp W regs mem md x ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_SCAN) regs mem md)
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_dec_ltP (m : nat) : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_decP D ly S Hp W regs mem md out w r Q ->
  (Q - Z.to_nat (r - (pi_p D + 1)) < m)%nat ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_DEC) regs mem md)
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_decP : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_decP D ly S Hp W regs mem md out w r Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_DEC) regs mem md)
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_uP : Prop :=
  forall m, psb_dec_ltP m ->
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_uP D ly S Hp W regs mem md out w r Q ->
  (Q - Z.to_nat (r - (pi_p D + 1)) <= m)%nat ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_U) regs mem md)
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_freeP : Prop :=
  forall D ly S Hp W regs mem md out Q, ps_pre CTX CW D -> psb_at_freeP D ly S Hp W regs mem md out Q ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (psb_pc PSB_FREE) regs mem md)
    (ps_postPR (wle' segs YGcfRehidePost.RZ_cf) CW D).
Definition psb_seg_ret0P : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0P D ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (psb_pc PSB_RET0) regs mem md) (ps_postP D).
Definition psb_seg_ret0PR (R : world segs -> world segs -> Prop) : Prop :=
  forall D ly S Hp W regs mem md, ps_pre CTX CW D -> ps_at_ret0PR R CW D ly S Hp W regs mem md ->
  SRrG segs R W (cfg_at segs (psb_pc PSB_RET0) regs mem md) (ps_postPR R CW D).
Lemma psb_seg_ret0P_R_wle : psb_seg_ret0P = psb_seg_ret0PR (@wle segs).
Proof. reflexivity. Qed.
Definition psb_seg_retokP : Prop :=
  forall D ly S Hp W regs mem md out w r Q, ps_pre CTX CW D -> psb_at_retokP D ly S Hp W regs mem md out w r Q ->
  SRr segs W (cfg_at segs (psb_pc PSB_RETOK) regs mem md) (ps_postP D).
Definition psb_dec_stepP : Prop :=
  forall m, psb_dec_ltP m -> psb_dec_ltP (S m).
Lemma psb_seg_dec_of_stepP : psb_dec_stepP -> psb_seg_decP.
Proof.
intros HST.
assert (ALL : forall m, psb_dec_ltP m).
{ induction m as [|m IH].
  - intros D ly S Hp W regs mem md out w r Q _ _ H. exfalso. lia.
  - exact (HST m IH). }
intros D ly S Hp W regs mem md out w r Q HP HA.
apply (ALL (Nat.succ (Q - Z.to_nat (r - (pi_p D + 1)))) D ly S Hp W regs mem md out w r Q HP HA).
apply Nat.lt_succ_diag_r.
Qed.
End gp.

(* ---- the stable statements are the P := (fun _ => True) instances, both ways ---- *)
#[local] Notation PT := (fun _ : word -> option byte => True).
Ltac psb_T_cut H := let Hc := fresh in
  first [ destruct H as (Hc & H); split; [apply ps_carryP_T; exact Hc | exact H]
        | destruct H as (Hc & H); split; [apply ps_ex_carryP_T; exact Hc | exact H]
        | destruct H as (Hc & H); split; [apply (proj2 (ps_carryP_T _ _ _ _ _ _ _ _ _ _ _ _)); exact Hc | exact H]
        | destruct H as (Hc & H); split; [apply (proj2 (ps_ex_carryP_T _ _ _ _ _ _ _ _ _ _)); exact Hc | exact H]
        | apply ps_at_ret0P_T; exact H
        | apply (proj2 (ps_at_ret0P_T _ _ _ _ _ _ _ _ _ _ _ _)); exact H ].
Ltac psb_T_post_dn := intros ? ? _ HQ; apply ps_postP_T; exact HQ.
Ltac psb_T_post_up := intros ? ? _ HQ; apply (proj2 (ps_postP_T _ _ _ _ _ _ _)); exact HQ.
Ltac psb_T_postR_dn := intros ? ? _ HQ; apply ps_postPR_T; exact HQ.
Ltac psb_T_postR_up := intros ? ? _ HQ; apply (proj2 (ps_postPR_T _ _ _ _ _ _ _ _)); exact HQ.
Lemma psb_seg_entry_of_True : psb_seg_entryP PT <-> psb_seg_entry.
Proof.
split.
- intros H D HP. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (H D HP I)|].
  psb_T_postR_dn.
- intros H D HP _. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf)); [exact (H D HP)|].
  psb_T_postR_up.
Qed.
Lemma psb_seg_scan_of_True : psb_seg_scanP PT <-> psb_seg_scan.
Proof.
split.
- intros H D ly S Hp W regs mem md x HP HA. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md x HP); psb_T_cut HA|]. psb_T_postR_dn.
- intros H D ly S Hp W regs mem md x HP HA. unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md x HP); psb_T_cut HA|]. psb_T_postR_up.
Qed.
Lemma psb_seg_dec_of_True : psb_seg_decP PT <-> psb_seg_dec.
Proof.
split.
- intros H D ly S Hp W regs mem md out w r Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out w r Q HP); psb_T_cut HA|]. psb_T_postR_dn.
- intros H D ly S Hp W regs mem md out w r Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out w r Q HP); psb_T_cut HA|]. psb_T_postR_up.
Qed.
Lemma psb_seg_free_of_True : psb_seg_freeP PT <-> psb_seg_free.
Proof.
split.
- intros H D ly S Hp W regs mem md out Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out Q HP); psb_T_cut HA|]. psb_T_postR_dn.
- intros H D ly S Hp W regs mem md out Q HP HA. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out Q HP); psb_T_cut HA|]. psb_T_postR_up.
Qed.
Lemma psb_seg_ret0_of_True : psb_seg_ret0P PT <-> psb_seg_ret0.
Proof.
split.
- intros H D ly S Hp W regs mem md HP HA. eapply SRr_mono; [apply (H D ly S Hp W regs mem md HP); psb_T_cut HA|]. psb_T_post_dn.
- intros H D ly S Hp W regs mem md HP HA. eapply SRr_mono; [apply (H D ly S Hp W regs mem md HP); psb_T_cut HA|]. psb_T_post_up.
Qed.
Lemma psb_seg_ret0R_of_True : forall R, psb_seg_ret0PR PT R <-> psb_seg_ret0R R.
Proof.
intros R. split.
- intros H D ly S Hp W regs mem md HP HA. eapply (SRrG_mono segs R);
    [apply (H D ly S Hp W regs mem md HP);
     first [apply ps_at_ret0PR_T; exact HA | apply (proj2 (ps_at_ret0PR_T _ _ _ _ _ _ _ _ _ _ _ _ _)); exact HA]|].
  psb_T_postR_dn.
- intros H D ly S Hp W regs mem md HP HA. eapply (SRrG_mono segs R);
    [apply (H D ly S Hp W regs mem md HP);
     first [apply ps_at_ret0PR_T; exact HA | apply (proj2 (ps_at_ret0PR_T _ _ _ _ _ _ _ _ _ _ _ _ _)); exact HA]|].
  psb_T_postR_up.
Qed.
Lemma psb_seg_retok_of_True : psb_seg_retokP PT <-> psb_seg_retok.
Proof.
split.
- intros H D ly S Hp W regs mem md out w r Q HP HA.
  eapply SRr_mono; [apply (H D ly S Hp W regs mem md out w r Q HP); psb_T_cut HA|]. psb_T_post_dn.
- intros H D ly S Hp W regs mem md out w r Q HP HA.
  eapply SRr_mono; [apply (H D ly S Hp W regs mem md out w r Q HP); psb_T_cut HA|]. psb_T_post_up.
Qed.
Lemma psb_dec_lt_of_True : forall m, psb_dec_ltP PT m <-> psb_dec_lt m.
Proof.
intros m. split.
- intros H D ly S Hp W regs mem md out w r Q HP HA Hm. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out w r Q HP); [psb_T_cut HA | exact Hm]|]. psb_T_postR_dn.
- intros H D ly S Hp W regs mem md out w r Q HP HA Hm. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H D ly S Hp W regs mem md out w r Q HP); [psb_T_cut HA | exact Hm]|]. psb_T_postR_up.
Qed.
Lemma psb_seg_u_of_True : psb_seg_uP PT <-> psb_seg_u.
Proof.
split.
- intros H m Hlt D ly S Hp W regs mem md out w r Q HP HA Hm. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H m (proj2 (psb_dec_lt_of_True m) Hlt) D ly S Hp W regs mem md out w r Q HP);
    [psb_T_cut HA | exact Hm]|]. psb_T_postR_dn.
- intros H m Hlt D ly S Hp W regs mem md out w r Q HP HA Hm. unfold SRr'.
  eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
    [apply (H m (proj1 (psb_dec_lt_of_True m) Hlt) D ly S Hp W regs mem md out w r Q HP);
    [psb_T_cut HA | exact Hm]|]. psb_T_postR_up.
Qed.

(* the whole walk from its generic-P entry stretch, instantiated per record at ps_mn D: the KIT TEXT at image B (the kit's
   cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record), PRH_FnReader.v f1ae32e3b2cd tparse_string_specX), at every record (PS_Gen's ps_holds_of_entryP,
   then ps_K0_of_records) *)
Lemma psb_holds_of_segsP :
  (forall P, srr_inv_laws segs P -> srr_inv_call segs P -> psb_seg_entryP P) ->
  tparse_string_specX (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK CTX CW.
Proof.
intros HE. apply (ps_K0_of_records (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK CTX CW).
apply (ps_holds_of_entryP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK CTX CW).
intros D HP. exact (HE (ps_mn D) (ps_mn_laws D) (ps_mn_call D) D HP (ps_mn_entry D)).
Qed.

End psb.
