(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_reply.asan's snprintf at __wrap_snprintf (0x421dc = SIGMA WS_snprintf, RT_pf_Tbl.v
   PF_WRAP_SNPRINTF) at the SRr level, for reply's ONE format, at a generic allocator relation ARx, with the FP state
   KEPT (route (C) of SNP-ROUTE.md (sha256 5a5fabe9f628; internal record) section 7.5).

   No function is walked here.  The walk is the evt-level interceptor chain in its keep-FP form, CHAIN_K below
   (RT_pf_stmt_k.v snprintf_icpt_stmt_k: ___interceptor_snprintf -> ___interceptor_vsnprintf -> musl vsnprintf ->
   ___interceptor_vfprintf -> musl vfprintf, proved from the GXAK keep-FP twin of GXA); this file feeds it the
   contract's premises on the normalized store and reads its post back, in the steps of a Theorem Labs lane's
   FMgxaSeam.v fm_vfprintf_seamP (a working branch 3242941dc96, :340-604). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_sites W_journal_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require VfprintfCall G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require RT_IImgA RT_gxa_calls RT_gxa_calls_mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FMgxaSeamCall RT_pf_stmt RT_pf_stmt_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_pf_Tbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Exec Mem Frame Cells Step MState Arr ITree.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0x ACeg RT_pf_kit RT_pf_bz FMgxa_bridge FMgxaSeamBase
FMgxaSeamCells FMgxaSeamFam FMgxaSeamPost FMgxaSeamShadow FMgxaSeamNorm FMgxaSeamNormG FMgxaSeamNormX FMgxaSeamPostX.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FMgxaSeamReadyX FMgxaSeamGuard FMgxaSeamShadowX
RT_pf_snp_pcom RT_pf_chain_k FMgxaSeamARX AD2l CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require ImageA Mem Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require R_m2s I_pcrr I_pchead I_pck I_qck I_pcxgram
I_pcxlist F_achk Shadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Printf_model Printf_text G_printf_core_common.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require G_pad G_pop_arg G_fmt_fp_lib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require AsanFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RStep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module GSA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_snfsink.
Module GVA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module GM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls_mem.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Module PK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt_k.

(* ---- the narrowed contract ---- *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Section c.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* asnprintf_realizes_xn: W_sites_x.v:392-420 asnprintf_realizes_x VERBATIM (its Section-local names applied to
   B ARx), plus FOUR premises right after `pf_parse fmt = Some ps`, each of which NARROWS the contract:
   - the pieces are reply's one format "%s %d ";
   - (M1) the format lies in the image's read-only data below the GOT word: 65536 <= f, f + |fmt| + 1 <= 0x9e658;
   - (M3) the %s string (the first argument, a3 = getr regs 13, its bytes by apf_arg_ok's astr_at) likewise, with
     the 8 bytes past its NUL: 65536 <= r13, r13 + |s| + 1 + 8 <= 0x9e658;
   - (M2) the destination lies above the image: GLOBALS_TOP = 0x5fb000 <= d (RT_pf_Tbl.v PF_GLOBALS_TOP =
     GXA's GLOBALS_TOP at A_img, RT_pf_kit.v globals_top_val).
   The chain needs exactly these: GXA's statement reads the format as image data (RT_pf_stmt_k.v:112,
   VFB_GUARD's `A + |fmt| <= sym 0x22e18`), its %s argument with the slack to its granule end apart from the
   destination and app_mem 7 bytes past each byte (GXA/G_printf_core_common.v:257-270), and its destination off the
   image (RT_pf_stmt_k.v:114).
   (a) this narrowing was granted (SNP-ROUTE.md (sha256 5a5fabe9f628; internal record) section 7.5; the location premises on the same ground,
       2026-10-30) because every walked application satisfies all four literally: W_rig_top.v:3028 (RIG_FMT,
       W_rig_top.v:1350), W_LLVMFuzzerTestOneInput_gone_p1.v:649 (p1_fmt / p1_ps, :114-116) and
       W_LLVMFuzzerTestOneInput_gone_p1_x.v:479 all pass "%s %d " at f = VAL (A_OBJ 20) = 0x20f80, the %s string
       "param_gesture" at VAL (A_OBJ 21) = 0x20f20 and a buffer in a live fake frame (frame_addr .. 1 fpos + 32).
       The lemmas san_M1 / san_M2_AR / san_M2_x / san_M3 below prove each premise from those applications' own facts.
   (b) The four other callers of the trampoline 0x421dc in fuzz_reply.asan are on no proved path and are walked
       nowhere in lib/A: libunwind UnwindCursor::getFunctionName (0x87528), vsyslog (0x91278) and
       __strftime_fmt_1 (0x9bc64, 0x9bc88).  If one of them is ever walked at another format or location, these
       premises are where it bites. *)
Definition asnprintf_realizes_xn (pc gotw guard : Z) : Prop :=
forall ly S Hp W regs mem md d n f fmt ps args T,
aguard_ok W mem gotw guard ->
ecall_pre_stk_x B ARx (3 * ESTACK) ly S Hp W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
1 <= n < 2 ^ 31 -> 0 < d -> 0 < f ->
astr_at W mem f (printf_facts_c.pf_bytes fmt) ->
printf_facts_c.pf_parse fmt = Some ps ->
ps = [printf_facts_c.Ps; printf_facts_c.PLit 32; printf_facts_c.Pd; printf_facts_c.PLit 32] ->
65536 <= f -> f + Z.of_nat (length fmt) + 1 <= FR_GOT_GUARD ->
(forall s, hd_error args = Some (printf_facts_c.APtr s) ->
  65536 <= bv_unsigned (getr regs 13) /\ bv_unsigned (getr regs 13) + Z.of_nat (length s) + 1 + 8 <= FR_GOT_GUARD) ->
PF_GLOBALS_TOP <= d ->
printf_facts_c.pf_text ps args = Some T ->
Z.of_nat (length T) < 2 ^ 31 - 1 ->
aread_ok (3 * ESTACK) W regs mem f (Z.of_nat (length fmt) + 1) ->
atail_vis W mem (f + Z.of_nat (length fmt)) ->
apf_args_ok (3 * ESTACK) W regs mem d n
[getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args ->
awrite_ok B (3 * ESTACK) ly S W regs mem d n ->
(* seven bytes past the buffer in application memory (W6 f4dbfd816b6, W_sites.v:315-319, mirrored) *)
amem_range d (n + 7) ->
rt_rom_view B W mem ->
SRr SEGS W (cfg_at SEGS pc regs mem md)
(art_post_x ARx (3 * ESTACK) ly S Hp W regs mem md (fun a => d <= a < d + n)
(fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
abytes_at W mem' d (printf_facts_c.pf_bytes (firstn (Z.to_nat (n - 1)) T ++ [0])))).

(* the narrowed contract is implied by the general one; since W_sites_x.v's asnprintf_realizes_x is narrowed in place
   (the same four premises, PF_GLOBALS_TOP there being W_sites.v's, the number of RT_pf_Tbl.v's), the two are the same
   proposition *)
Lemma asnprintf_realizes_xn_of_x : forall pc gotw guard,
  asnprintf_realizes_x B ARx pc gotw guard -> asnprintf_realizes_xn pc gotw guard.
Proof. intros pc gotw guard H. exact H. Qed.

End c.
End b.
End a.

(* ---- the one format: the parser is injective, the text has one shape ---- *)
Module PFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.printf_facts_c.

Definition pf_unparse_piece (p : PFC.pf_piece) : list Z :=
  match p with
  | PFC.PLit b => [b] | PFC.Pd => [37; 100] | PFC.Pc => [37; 99] | PFC.Px04 => [37; 48; 52; 120]
  | PFC.Px02 => [37; 48; 50; 120] | PFC.Pllu => [37; 108; 108; 117] | PFC.Ps => [37; 115]
  | PFC.Pps => [37; 46; 42; 115]
  end.
Definition pf_unparse (ps : list PFC.pf_piece) : list Z := flat_map pf_unparse_piece ps.

Lemma pf_parse_unparse : forall n f ps, (length f <= n)%nat -> PFC.pf_parse f = Some ps -> f = pf_unparse ps.
Proof.
induction n as [|n IH]; intros f ps Hn H.
- destruct f as [|b r]; [cbn in H; injection H as <-; reflexivity | cbn in Hn; lia].
- destruct f as [|b r]; [cbn in H; injection H as <-; reflexivity|]. cbn [length] in Hn.
  cbn [PFC.pf_parse] in H. destruct (b =? 37) eqn:E37.
  + apply Z.eqb_eq in E37. subst b. destruct r as [|c r1]; [discriminate H|]. cbn [length] in Hn.
    assert (OM : forall (p : PFC.pf_piece) l rest, (length l <= n)%nat ->
              option_map (cons p) (PFC.pf_parse l) = Some ps -> 37 :: c :: rest = pf_unparse_piece p ++ l ->
              37 :: c :: rest = pf_unparse ps).
    { intros p l rest Hl Ho Er. destruct (PFC.pf_parse l) as [ps'|] eqn:El; [|discriminate Ho].
      cbn in Ho. injection Ho as <-. rewrite Er, (IH l ps' Hl El). reflexivity. }
    destruct (c =? 100) eqn:Ec1; [apply Z.eqb_eq in Ec1; subst c; exact (OM PFC.Pd r1 r1 ltac:(lia) H eq_refl)|].
    destruct (c =? 99) eqn:Ec2; [apply Z.eqb_eq in Ec2; subst c; exact (OM PFC.Pc r1 r1 ltac:(lia) H eq_refl)|].
    destruct (c =? 115) eqn:Ec3; [apply Z.eqb_eq in Ec3; subst c; exact (OM PFC.Ps r1 r1 ltac:(lia) H eq_refl)|].
    destruct (c =? 48) eqn:Ec4.
    { apply Z.eqb_eq in Ec4. subst c. destruct r1 as [|c2 [|c3 r3]]; try discriminate H. cbn [length] in Hn.
      destruct ((c2 =? 52) && (c3 =? 120)) eqn:E2.
      - apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
        exact (OM PFC.Px04 r3 _ ltac:(lia) H eq_refl).
      - destruct ((c2 =? 50) && (c3 =? 120)) eqn:E3; [|discriminate H].
        apply andb_prop in E3 as [E3a E3b]. apply Z.eqb_eq in E3a, E3b. subst c2 c3.
        exact (OM PFC.Px02 r3 _ ltac:(lia) H eq_refl). }
    destruct (c =? 108) eqn:Ec5.
    { apply Z.eqb_eq in Ec5. subst c. destruct r1 as [|c2 [|c3 r3]]; try discriminate H. cbn [length] in Hn.
      destruct ((c2 =? 108) && (c3 =? 117)) eqn:E2; [|discriminate H].
      apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
      exact (OM PFC.Pllu r3 _ ltac:(lia) H eq_refl). }
    destruct (c =? 46) eqn:Ec6; [|discriminate H].
    apply Z.eqb_eq in Ec6. subst c. destruct r1 as [|c2 [|c3 r3]]; try discriminate H. cbn [length] in Hn.
    destruct ((c2 =? 42) && (c3 =? 115)) eqn:E2; [|discriminate H].
    apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
    exact (OM PFC.Pps r3 _ ltac:(lia) H eq_refl).
  + destruct ((0 <? b) && (b <? 256)); [|discriminate H].
    destruct (PFC.pf_parse r) as [ps'|] eqn:Er; [|discriminate H]. cbn in H. injection H as <-.
    rewrite (IH r ps' ltac:(lia) Er). reflexivity.
Qed.

Definition snp_fmtb : list Z := [37; 115; 32; 37; 100; 32].   (* "%s %d " *)
Definition snp_ps : list PFC.pf_piece := [PFC.Ps; PFC.PLit 32; PFC.Pd; PFC.PLit 32].

Lemma snp_fmt_eq : forall fmt, PFC.pf_parse fmt = Some snp_ps -> fmt = snp_fmtb.
Proof. intros fmt H. exact (pf_parse_unparse (length fmt) fmt snp_ps (le_n _) H). Qed.

Lemma snp_text_shape : forall args T, PFC.pf_text snp_ps args = Some T ->
  exists s v, args = [PFC.APtr s; PFC.AInt v] /\ T = s ++ 32 :: PFC.pf_dec v ++ [32].
Proof.
intros args T H. unfold snp_ps in H.
destruct args as [|[v0|u0|s] args]; cbn in H; try discriminate H.
destruct args as [|[v|u|s'] args]; cbn in H; try discriminate H.
destruct args as [|a args]; cbn in H; [|discriminate H].
injection H as <-. exists s, v. split; reflexivity.
Qed.

(* the byte view of a string and its NUL, as values *)
Lemma snp_nth_pf_bytes : forall s i, Forall (fun c => 0 < c < 256) s -> (i <= length s)%nat ->
  bv_unsigned (nth i (PFC.pf_bytes s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) = nth i (s ++ [0]) 0.
Proof.
induction s as [|c s IH]; intros i HF Hi.
- cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. reflexivity.
- inversion HF as [|? ? Hc HF']; subst. destruct i as [|i].
  + cbn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
  + cbn [length] in Hi. exact (IH i HF' ltac:(lia)).
Qed.

(* GX's decimal renderer is printf_facts_c's (FMpfArmPdSeam.v's pt_pf_dec_d, for this copy of the renderer) *)
Module PTx := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.Printf_text.
Lemma snp_pf_digits_eq : forall fuel x acc, PTx.pf_digits fuel x acc = PFC.pf_digits fuel x acc.
Proof.
induction fuel as [|k IH]; intros x acc; [reflexivity|].
cbn [PTx.pf_digits PFC.pf_digits]. destruct (x <? 10); [reflexivity | apply IH].
Qed.
Lemma snp_pf_dec_eq : forall v, PTx.pf_dec v = PFC.pf_dec v.
Proof. intros v. unfold PTx.pf_dec, PFC.pf_dec. rewrite !snp_pf_digits_eq. reflexivity. Qed.

(* ---- THE NARROWING IS SATISFIED AT ITS THREE APPLICATIONS (W_rig_top.v:3028, W_LLVMFuzzerTestOneInput_gone_p1.v:649,
   W_LLVMFuzzerTestOneInput_gone_p1_x.v:479), each premise from the facts the application itself holds there ---- *)
Section San. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* M1: all three pass f = VAL (A_OBJ 20) (lib/A/W_LLVMFuzzerTestOneInput_gone_p1.v:623 V20; gone_p1_x.v:476 and W_rig_top.v:3028 the same object at
   PB_fr) and a format that parses to the four pieces (RIG_FMT, p1_fmt), so |fmt| = 6 *)
Lemma san_M1 : forall fmt, PFC.pf_parse fmt = Some snp_ps ->
  65536 <= @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) /\
  @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) + Z.of_nat (length fmt) + 1 <= FR_GOT_GUARD.
Proof.
intros fmt H. rewrite (snp_fmt_eq fmt H).
assert (V20 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) = 135040) by (vm_compute; reflexivity).
rewrite V20. unfold FR_GOT_GUARD. cbn [length snp_fmtb]. lia.
Qed.

(* M3: all three pass a3 = VAL (A_OBJ 21) (gone_p1.v:679 U13, W_rig_top.v:3247 R13) with the arguments
   [APtr K_GESTURE; AInt id] (lib/A/W_LLVMFuzzerTestOneInput_gone_p1.v:649, gone_p1_x.v:477, W_rig_top.v:3241), so |s| = 13 *)
Lemma san_M3 : forall (r13 : word) (id : Z) s, bv_unsigned r13 = @pa_val _ fr_prog_listing PB_fr (A_OBJ 21) ->
  hd_error [PFC.APtr RelayModel.K_GESTURE; PFC.AInt id] = Some (PFC.APtr s) ->
  65536 <= bv_unsigned r13 /\ bv_unsigned r13 + Z.of_nat (length s) + 1 + 8 <= FR_GOT_GUARD.
Proof.
intros r13 id s E H. cbn in H. injection H as <-.
assert (V21 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 21) = 134944) by (vm_compute; reflexivity).
rewrite E, V21. unfold FR_GOT_GUARD, RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

(* M2 at the two AR applications: the buffer is frame_addr ly 1 fpos + 32 for a live class-1 fake frame (W_rig_top.v:3004
   HAR / Hin / HF from ts_jframe; gone_p1.v:508-509 FF / Hfin with HART).  AR's ledger puts ly_img over every segment
   (W_img.fr_img_cover: its top is at least 0x5fb000), and a fake frame lies above ly_img: the fake stack is disjoint
   from ly_img (YG0s.frame_facts), starts at or above 4096 and is longer than kImgLo (layout_ok's lo_img) - YCbqG.v's
   field-17 argument (:1306-1315) *)
Lemma san_M2_AR : forall B ly S (W : world frsegs) mem md fpos,
  AR frsegs B ly S W mem md -> In (1, fpos) (frames S) -> PF_GLOBALS_TOP <= frame_addr ly 1 fpos + 32.
Proof.
intros B ly S W mem md fpos HAR Hin. pose proof HAR as (M & LG & _).
destruct (fr_img_cover ly S md LG) as [_ C2].
pose proof (lo_img _ (am_layout _ _ _ _ M)) as (I1 & I2 & _).
destruct (YG0s.frame_facts B ly S _ 1 fpos M Hin) as (C1 & _ & [F1 _] & D & _ & P1 & _).
assert (HF : fst (ly_img ly) + snd (ly_img ly) <= ly_F ly).
{ destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt|Hge]; [|exact Hge].
  exfalso. apply D. exists (Z.max (ly_F ly) (fst (ly_img ly))). unfold in_zr. cbn [fst snd].
  unfold kImgLo, kFakeStackSize in *. split; [lia | left; lia]. }
unfold frame_addr, kFakeFramesOff, PF_GLOBALS_TOP in *. lia.
Qed.

(* M2 at the ARx application (gone_p1_x.v:476, FF := frame_addr ly 1 fpos at the walk's AR0 state): the laws' image
   field alx_img puts the frame above ly_img, whose top is at least 0x5fb000 (W_img_x.fr_img_cover_x) *)
Lemma san_M2_x : forall B (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop)
  hl, AR_laws_x frsegs B ARx hl ->
  forall ly S Hp W mem md fpos, ARx ly S Hp W mem md -> In (1, fpos) (frames S) ->
  PF_GLOBALS_TOP <= frame_addr ly 1 fpos + 32.
Proof.
intros B ARx hl LX ly S Hp W mem md fpos HAR Hin.
destruct (W_img_x.fr_img_cover_x B ARx LX ly S Hp W mem md HAR) as [_ C2].
destruct (alx_img _ _ _ LX ly S Hp W mem md HAR) as [_ HF].
pose proof (HF 1 fpos Hin) as HF1. unfold PF_GLOBALS_TOP. lia.
Qed.
End San.

(* ---- the guard of GXA's closed musl vfprintf body at reply's three interceptor contracts: RT_pf_chain.v's fr_vfb
   (the type of RT_gxa_inst.fr_vfprintf_guarded GM.copy_ready .. GM.set_ready .. GC.strn_ready .. INV,
   G_vfprintf_snf_closed.v:117-118) at the seam's invariant INV := FMgxaSeamCall.SEAM_INV ---- *)
#[local] Existing Instance RT_IImgA.A_img.
Definition VFB_GUARD : VFC.vf_guard :=
  GVA.vf_ready_a (GSA.snf_out_ready GM.copy_ready) GM.set_ready GC.strn_ready GM.copy_ready
    FMgxaSeamCall.SEAM_INV.

(* ---- the seam's generic helpers (a Theorem Labs lane's FMgxaSeam.v:85-190, relocated: reply's GOT word / guard numerals) ---- *)
Module RE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Module CJE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Exec.
Module CJMm := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Module SBa := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamBase.
Module SPo := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamPost.

Lemma sa_mstep_eqv : forall sg a a' b, CJE.mstep sg a b -> RE.ms_eqv a a' ->
  exists b', CJE.mstep sg a' b' /\ RE.ms_eqv b b'.
Proof.
intros sg a a' b [Hsvc Hst] E.
pose proof (RE.step_accesses_eqv sg a a' E) as R.
pose proof E as (_ & _ & _ & Hs & _).
unfold RiscvSemantics.step in Hst. unfold CJE.mstep, RiscvSemantics.step.
revert R Hst.
destruct (RiscvSemantics.step_accesses sg a) as [[x acc]| |];
destruct (RiscvSemantics.step_accesses sg a') as [[y acc']| |];
cbn [RE.rep_eqv RiscvSemantics.drop_access_report RiscvSemantics.access_value RiscvSemantics.accessed_ranges];
intros R Hst; try discriminate; try contradiction.
injection Hst as <-. destruct R as [Hxy _].
exists y. split; [split; [congruence | reflexivity] | exact Hxy].
Qed.

Lemma sa_msteps_eqv : forall sg a b, CJE.msteps sg a b ->
  forall a', RE.ms_eqv a a' -> exists b', CJE.msteps sg a' b' /\ RE.ms_eqv b b'.
Proof.
intros sg a b H. induction H as [ms | ms ms1 ms2 Hs _ IH]; intros a' E.
- exists a'. split; [apply CJE.msteps_refl | exact E].
- destruct (sa_mstep_eqv sg ms a' ms1 Hs E) as (b1 & Hs' & E1).
  destruct (IH b1 E1) as (b2 & H2 & E2).
  exists b2. split; [eapply CJE.msteps_cons; eassumption | exact E2].
Qed.

Lemma sa_evt_eqv : forall sg (Q : machine_state -> Prop) a a', CJE.evt sg Q a -> RE.ms_eqv a a' ->
  CJE.evt sg (fun x => exists y, Q y /\ RE.ms_eqv y x) a'.
Proof.
intros sg Q a a' (b & Hb & HQ) E.
destruct (sa_msteps_eqv sg a b Hb a' E) as (b' & Hb' & E').
exists b'. split; [exact Hb' | exists b; split; assumption].
Qed.

Lemma sa_getr_nz : forall (R : bvmap 5 word) (r : bv 5), is_x0 r = false -> getr R r = reg_get R r.
Proof. intros R r H. unfold getr. rewrite bv_eqb0_is_x0, H. reflexivity. Qed.

(* the GOT word of __stack_chk_guard and the guard itself lie in writable segments of fuzz_reply.asan *)
Lemma sa_ssp_writable : forall (m : word -> option byte) a,
  (FR_GOT_GUARD <= a < FR_GOT_GUARD + 8) \/ (FR_GUARD <= a < FR_GUARD + 8) -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold FR_GOT_GUARD, FR_GUARD in Ha. unfold writable_at, wview.
destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
assert (L : a = 0x9e658 \/ a = 0x9e659 \/ a = 0x9e65a \/ a = 0x9e65b \/ a = 0x9e65c \/ a = 0x9e65d \/
            a = 0x9e65e \/ a = 0x9e65f \/ a = 0x5f94b0 \/ a = 0x5f94b1 \/ a = 0x5f94b2 \/ a = 0x5f94b3 \/
            a = 0x5f94b4 \/ a = 0x5f94b5 \/ a = 0x5f94b6 \/ a = 0x5f94b7) by lia.
repeat (destruct L as [L|L]; [subst a; vm_compute; discriminate|]).
subst a. vm_compute. discriminate.
Qed.

Section hk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a byte the store may write is a byte the harness reads *)
Lemma sa_writable_aview : forall H mem a,
  writable_at tfibsegs (SBa.cjstore H mem) a -> aview tfibsegs H mem a <> None.
Proof.
intros H mem a HW. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate|].
pose proof (SPo.seg_rom_of_wview (SBa.cjstore H mem) (Z_to_bv 64 a) HW E) as R.
destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | contradiction].
Qed.

(* ... and the world does not hide it *)
Lemma sa_writable_vis : forall (W : world tfibsegs) mem a,
  writable_at tfibsegs (SBa.cjstore (w_H W) mem) a -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W mem a HW. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso. apply HW.
unfold wview, SBa.cjstore, mrestrict. rewrite E, (w_Hoff W _ E). reflexivity.
Qed.
End hk.

(* ---- the image's owned read-only bytes are pinned by AF0m's const cells (W_LLVMFuzzerTestOneInput_G.v:562-650,
   copied: that file's closure is the whole cut walk) ---- *)
Definition snp_num_of (e : YG0f.aexp) : option Z := match e with YG0f.ANum z => Some z | _ => None end.
Definition snp_av_num (v : YG0f.aval) : option Z := match v with YG0f.AV (YG0f.ANum z) => Some z | _ => None end.
Lemma snp_num_of_some : forall e z, snp_num_of e = Some z -> e = YG0f.ANum z.
Proof. intros e z H. destruct e; cbn in H; congruence. Qed.
Lemma snp_av_num_some : forall v z, snp_av_num v = Some z -> v = YG0f.AV (YG0f.ANum z).
Proof. intros v z H. destruct v as [e|m w]; [destruct e|]; cbn in H; congruence. Qed.
Definition snp_rng_all (f : Z -> bool) (r : Z * Z) : bool :=
  forallb (fun i => f (fst r + Z.of_nat i)) (seq 0 (Z.to_nat (snd r))).
Definition snp_romb (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs.
Lemma snp_romb_of : forall a, in_rom tfibsegs a -> snp_romb a = true.
Proof.
intros a (sg & Hs & Hw & Hr). unfold snp_romb. apply existsb_exists. exists sg. split; [exact Hs|].
rewrite Hw. cbn [negb andb]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition snp_pin_ok (a : Z) (c : YG0f.acell) : bool :=
  match snp_num_of (YG0f.c_at c), snp_av_num (YG0f.c_val c) with
  | Some z, Some v =>
      if (z <=? a) && (a <? z + Z.of_nat (YG0f.c_w c)) then
        match YK11.seg_rom tfibsegs (Z_to_bv 64 a) with
        | Some b => YG0f.le_byte v (YG0f.c_w c) (Z.to_nat (a - z)) =? bv_unsigned b
        | None => false
        end
      else false
  | _, _ => false
  end.
Lemma snp_pin_ok_spec : forall a c, snp_pin_ok a c = true -> exists z v,
  YG0f.c_at c = YG0f.ANum z /\ YG0f.c_val c = YG0f.AV (YG0f.ANum v) /\ z <= a < z + Z.of_nat (YG0f.c_w c) /\
  Some (YG0f.le_byte v (YG0f.c_w c) (Z.to_nat (a - z))) =
    option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
intros a c H. unfold snp_pin_ok in H.
destruct (snp_num_of (YG0f.c_at c)) as [z|] eqn:E1; [|discriminate].
destruct (snp_av_num (YG0f.c_val c)) as [v|] eqn:E2; [|discriminate].
exists z, v. apply snp_num_of_some in E1. apply snp_av_num_some in E2.
destruct ((z <=? a) && (a <? z + Z.of_nat (YG0f.c_w c))) eqn:H1; [|discriminate].
apply andb_prop in H1 as [H1a H1b]. apply Z.leb_le in H1a. apply Z.ltb_lt in H1b.
split; [exact E1|]. split; [exact E2|]. split; [lia|].
destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; [|discriminate]. apply Z.eqb_eq in H. cbn. rewrite H.
reflexivity.
Qed.
Definition snp_rom_free (r : Z * Z) : bool :=
  forallb (fun sg => seg_writable sg || (fst r + snd r <=? Z.of_N (seg_base sg)) ||
    (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? fst r)) tfibsegs.
Lemma snp_rom_free_ok : forall r a, snp_rom_free r = true -> in_zr a r -> in_rom tfibsegs a -> False.
Proof.
intros r a H Hz (sg & Hs & Hw & Hr). unfold snp_rom_free in H. rewrite forallb_forall in H. specialize (H sg Hs).
rewrite Hw in H. cbn [orb] in H. unfold in_zr in Hz.
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Definition snp_owned_rom_pinned_b : bool :=
  forallb (fun r => if snp_rom_free r then true else
    snp_rng_all (fun a => if snp_romb a then existsb (snp_pin_ok a) Tfib_const_abs else true) r) Tfib_owned_static.
Lemma snp_owned_rom_pinned_ok : snp_owned_rom_pinned_b = true.
Proof. vm_compute. reflexivity. Qed.

Section rp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma snp_rom_pinned : forall B, TfibSyms B ->
  forall a, in_rom tfibsegs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned tfibsegs B a.
Proof.
intros B TS a Hr Ho ly.
rewrite (ts_owned B TS) in Ho.
pose proof snp_owned_rom_pinned_ok as HO. unfold snp_owned_rom_pinned_b in HO. rewrite forallb_forall in HO.
apply Exists_exists in Ho as (r & Hr' & Hz).
specialize (HO r Hr'). destruct (snp_rom_free r) eqn:Hfree; [exfalso; exact (snp_rom_free_ok r a Hfree Hz Hr)|].
unfold snp_rng_all in HO. rewrite forallb_forall in HO. unfold in_zr in Hz.
specialize (HO (Z.to_nat (a - fst r)) ltac:(apply in_seq; lia)).
replace (fst r + Z.of_nat (Z.to_nat (a - fst r))) with a in HO by lia.
rewrite (snp_romb_of a Hr) in HO.
apply existsb_exists in HO as (c & Hc & Hp).
destruct (snp_pin_ok_spec a c Hp) as (z & v & Ea & Ev & Hzr & Hbyte).
exists c, (YG0f.ANum v).
rewrite (ts_const B TS ly). unfold Tfib_const.
split; [apply in_or_app; right; apply in_or_app; left; exact Hc|].
split; [exact Ev|]. rewrite Ea. cbn [YG0f.aeval]. split; [exact Hzr | exact Hbyte].
Qed.
End rp.

Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNorm.
Module MN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module CJS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.
Module CJC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Cells.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module CJMS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Module PM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.Printf_model.
Module PT := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.Printf_text.
Module GXI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module PRL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec.Prelim.
Module GFP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_fmt_fp_lib.
Module GPAD := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Module NG := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNormG.
Module RStep := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module CJArr := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Arr.
Module AF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Module SRy := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamReadyX.
Module BzI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Module BzM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Module BzCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Module BzR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Module SGd := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamGuard.
Module ShX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamShadowX.
Module GCA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GCC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.StrnlenCall.
Module BSF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Spec.StrFun.
(* ---- the theorem ---- *)
Section snp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable hl : Z.
(* the allocator laws (top_x's ARX_laws at reply's instance); their alx_const_cells is the runtime constant-cell
   law of a Theorem Labs lane's lib/Rt/RTx.v rt_laws (rtl_const_cells, = rt_laws_of_x's YCbqG.alx_const_cells) *)
Hypothesis LAWS : YCbqG.AR_laws_x tfibsegs B ARx hl.
(* FMgxaSeamARX.v's two side laws, verbatim (proved there at ARX: ARX_LAY, ARX_BANDP) *)
Hypothesis LAY : forall ly S Hp (W : world tfibsegs) mem md, ARx ly S Hp W mem md -> layout_ok ly.
Hypothesis BANDP : forall ly S Hp (W : world tfibsegs) mem md a, ARx ly S Hp W mem md -> in_band_rw a ->
  w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview tfibsegs (w_H W) mem a <> None.
Hypothesis TB : TfibSyms B.
(* the world field w_H8 (a working branch), in its field form until it lands *)
Hypothesis W_H8 : forall (W : world tfibsegs) a, in_band_rw a ->
  w_H W (Z_to_bv 64 a) = w_H W (Z_to_bv 64 (a - a mod 8)).
(* the keep-FP evt chain at __wrap_snprintf *)
Hypothesis CHAIN_K : PK.snprintf_icpt_stmt_k GM.set_ready (PS.vf_ready_icpt VFB_GUARD).
(* REAL(vsnprintf) = musl vsnprintf (RT_pf_bz.v:42 sni_cells' last cell), in HGOTG's shape (gone_p1_x.v:97).  TRUE at
   the pin: the cell 0x9f770 is in the RW PT_LOAD at 0x9f6e0, and the ELF's file bytes there are 0x95e34 (every Bz
   interceptor walk was relocated with it, Bz/K/I_vsnprintfw.v:253).  AF0m.v's Tfib_const has no row for it (it has
   0x9f760 :120 and 0x9f768 :121), so no law gives it yet; it is discharged by alx_const_cells in the commit that takes
   the new AF0m row (regenerated on its own side branch). *)
Hypothesis REALVSN : forall ly S Hp (W : world tfibsegs) mem md, ARx ly S Hp W mem md ->
  rdword (aview tfibsegs (w_H W) mem) PF_REAL_VSNPRINTF = Some PF_MUSL_VSNPRINTF.


(* the read agreement the normalized store needs (MemNorm.ro_agree): a read-only byte of the image reads its ELF
   byte.  Not owned: rt_rom_view (the errno cell is in .bss); owned: AF0m's pin (snp_rom_pinned) through the const
   cells law (W_journal_x.rom_pinned_view_x) *)
Lemma snp_ro_agree : forall ly S Hp (W : world tfibsegs) mem md, ARx ly S Hp W mem md ->
  rt_rom_view (PI := PB_fr) B W mem -> MN.ro_agree tfibsegs (SBa.cjstore (w_H W) mem).
Proof.
intros ly S Hp W mem md HAR HRV a Hro.
pose proof (NM.tfib_ro_range a Hro) as Hr.
assert (Hrom : in_rom tfibsegs (bv_unsigned a)).
{ assert (Hro' : CJMm.ro_addr tfibsegs a = true) by exact Hro. unfold CJMm.ro_addr in Hro'.
  destruct (find_segment tfibsegs (bv_unsigned a) 1) as [sg|] eqn:Hf; [|discriminate Hro'].
  destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & H1 & H2).
  exists sg. split; [exact Hin|]. split; [apply negb_true_iff in Hro'; exact Hro' | lia]. }
assert (E : aview tfibsegs (w_H W) mem (bv_unsigned a) =
            option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (bv_unsigned a)))).
{ assert (Hd : forall r, {in_zr (bv_unsigned a) r} + {~ in_zr (bv_unsigned a) r}).
  { intros [lo len]. unfold in_zr. cbn [fst snd].
    destruct (Z_le_dec lo (bv_unsigned a)); [destruct (Z_lt_dec (bv_unsigned a) (lo + len))|];
      [left | right | right]; lia. }
  destruct (Exists_dec (in_zr (bv_unsigned a)) (as_owned_static B) Hd) as [Hown | Hno].
  - exact (rom_pinned_view_x tfibsegs B ARx LAWS ly S Hp W mem md _ HAR (snp_rom_pinned B TB _ Hrom Hown)).
  - apply (HRV (bv_unsigned a) Hrom Hno). unfold aerrno_cell. rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia. }
rewrite SBa.aview_mrd in E.
assert (Ha : CJMm.wa (bv_unsigned a) = a) by (unfold CJMm.wa; apply Z_to_bv_bv_unsigned).
rewrite Ha, Z_to_bv_bv_unsigned in E.
change (CJMm.mrd tfibsegs (SBa.cjstore (w_H W) mem) a = YK11.seg_rom tfibsegs a).
revert E.
destruct (CJMm.mrd tfibsegs (SBa.cjstore (w_H W) mem) a) as [b|], (YK11.seg_rom tfibsegs a) as [c|];
  cbn [option_map]; intros E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ---- the runtime cells the chain reads: ARx's const cells (and REALVSN's), at every store that keeps the
   normalized store's bytes of the image's writable part [0x9d000, 0x5fb000) ---- *)
Definition snp_img_agree (m0 m' : word -> option byte) : Prop :=
  forall x : word, 0x9d000 <= bv_unsigned x < 0x5fb000 -> m' x = m0 x.

Lemma snp_val_mem_agree : forall (m m' : word -> option byte) a (w : nat) v,
  (forall k, (k < w)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs m a w v -> val_mem tfibsegs m' a w v.
Proof. intros m m' a w v E H k Hk. pose proof (H k Hk) as Hb. unfold mbyte in *. rewrite (E k Hk). exact Hb. Qed.

(* the normalized store keeps every byte of the image's writable part *)
Lemma snp_keep_img : forall ly R (W : world tfibsegs) mem (x : word), 0x9d000 <= bv_unsigned x < 0x5fb000 ->
  NM.cjnormv ly R (w_H W) mem x = SBa.cjstore (w_H W) mem x.
Proof.
intros ly R W mem x Hx.
assert (Hsd : NM.seam_drop ly R x = false).
{ rewrite (NM.seam_drop_app ly R x ltac:(unfold AF.app_mem, AF.LOWMEM_END; lia)).
  apply NM.keep_of_writable; [apply NM.ro_addr_off; right; lia | unfold TASK_SIZE; lia]. }
unfold NM.cjnormv, NG.gdrop_normalize. rewrite Hsd. reflexivity.
Qed.

Lemma snp_const_val : forall ly S Hp (W : world tfibsegs) mem md a (w : nat) v,
  ARx ly S Hp W mem md ->
  AF0x.cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a w v.
Proof.
intros ly S Hp W mem md a w v HAR E.
apply (AF0x.cell_holds_val_mem B ly (w_H W) mem (ANum a) w (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly))
         (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR)).
rewrite (ts_const B TB ly). exact (AF0x.cell_lookup_In _ _ _ E).
Qed.

Lemma snp_agree_at : forall ly R (W : world tfibsegs) mem (m' : word -> option byte) a (w : nat),
  snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> 0x9d000 <= a -> a + Z.of_nat w <= 0x5fb000 ->
  forall k, (k < w)%nat ->
    m' (Z_to_bv 64 (a + Z.of_nat k)) = mrestrict (w_H W) mem (Z_to_bv 64 (a + Z.of_nat k)).
Proof.
intros ly R W mem m' a w AG H1 H2 k Hk.
assert (Hx : bv_unsigned (Z_to_bv 64 (a + Z.of_nat k)) = a + Z.of_nat k) by (apply FMupoison.wz; lia).
rewrite (AG _ ltac:(rewrite Hx; lia)), snp_keep_img by (rewrite Hx; lia).
unfold SBa.cjstore, mrestrict. destruct (w_H W (Z_to_bv 64 (a + Z.of_nat k))); reflexivity.
Qed.

Lemma snp_c8 : forall ly S Hp (W : world tfibsegs) mem md R (m' : word -> option byte) a v,
  ARx ly S Hp W mem md -> snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' ->
  AF0x.cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 8 (AV (ANum v))) ->
  0x9d000 <= a -> a + 8 <= 0x5fb000 -> 0 <= v < 2 ^ 64 ->
  BzSt.ro_cells BzI.asegs m' a [BzCl.C8 (Z_to_bv 64 v)].
Proof.
intros ly S Hp W mem md R m' a v HAR AG E H1 H2 Hv.
apply SRy.c8_of_val_mem; [lia | lia | exact Hv |].
apply (snp_val_mem_agree (mrestrict (w_H W) mem)); [|exact (snp_const_val ly S Hp W mem md a 8 v HAR E)].
exact (snp_agree_at ly R W mem m' a 8 AG H1 ltac:(cbn; lia)).
Qed.

Lemma snp_c1 : forall ly S Hp (W : world tfibsegs) mem md R (m' : word -> option byte) a v,
  ARx ly S Hp W mem md -> snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' ->
  AF0x.cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 1 (AV (ANum v))) ->
  0x9d000 <= a -> a + 1 <= 0x5fb000 -> 0 <= v < 256 ->
  BzSt.ro_cells BzI.asegs m' a [BzCl.C1 (Z_to_bv 8 v)].
Proof.
intros ly S Hp W mem md R m' a v HAR AG E H1 H2 Hv.
apply SRy.c1_of_val_mem; [lia | lia | exact Hv |].
apply (snp_val_mem_agree (mrestrict (w_H W) mem)); [|exact (snp_const_val ly S Hp W mem md a 1 v HAR E)].
exact (snp_agree_at ly R W mem m' a 1 AG H1 ltac:(cbn; lia)).
Qed.

(* REAL(vsnprintf), from REALVSN *)
Lemma snp_realvsn_cell : forall ly S Hp (W : world tfibsegs) mem md R (m' : word -> option byte),
  ARx ly S Hp W mem md -> snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' ->
  BzSt.ro_cells BzI.asegs m' PF_REAL_VSNPRINTF [BzCl.C8 (Z_to_bv 64 PF_MUSL_VSNPRINTF)].
Proof.
intros ly S Hp W mem md R m' HAR AG.
apply SRy.c8_of_val_mem; [unfold PF_REAL_VSNPRINTF; lia | unfold PF_REAL_VSNPRINTF; lia |
  unfold PF_MUSL_VSNPRINTF; lia |].
apply (snp_val_mem_agree (mrestrict (w_H W) mem)).
- exact (snp_agree_at ly R W mem m' PF_REAL_VSNPRINTF 8 AG ltac:(unfold PF_REAL_VSNPRINTF; lia)
           ltac:(unfold PF_REAL_VSNPRINTF; cbn; lia)).
- eapply YCbq.val_mem_of_rdword. exact (REALVSN ly S Hp W mem md HAR).
Qed.

Local Ltac snp_c8t HAR AG := eapply (snp_c8 _ _ _ _ _ _ _ _ _ _ HAR AG); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac snp_c1t HAR AG := eapply (snp_c1 _ _ _ _ _ _ _ _ _ _ HAR AG); [vm_compute; reflexivity | lia | lia | lia].

(* ___interceptor_snprintf's / ___interceptor_vsnprintf's cells (RT_pf_bz.v sni_cells) *)
Lemma snp_sni_cells : forall ly S Hp (W : world tfibsegs) mem md R (m' : word -> option byte),
  ARx ly S Hp W mem md -> snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> RT_pf_bz.sni_cells m'.
Proof.
intros ly S Hp W mem md R m' HAR AG.
unfold RT_pf_bz.sni_cells, PF_ASAN_INITED, PF_GOT_COMMON_FLAGS, PF_COMMON_FLAGS, PF_CHECK_PRINTF.
split; [|split; [|split]].
- apply SRy.rw_of_ro; [snp_c1t HAR AG | vm_compute; reflexivity].
- snp_c8t HAR AG.
- snp_c1t HAR AG.
- exact (snp_realvsn_cell ly S Hp W mem md R m' HAR AG).
Qed.

(* ___interceptor_vfprintf's cells (RT_pf_bz.v vfi_cells) *)
Lemma snp_vfi_cells : forall ly S Hp (W : world tfibsegs) mem md R (m' : word -> option byte),
  ARx ly S Hp W mem md -> snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> RT_pf_bz.vfi_cells m'.
Proof.
intros ly S Hp W mem md R m' HAR AG.
unfold RT_pf_bz.vfi_cells, PF_ASAN_INITED, PF_GOT_COMMON_FLAGS, PF_COMMON_FLAGS, PF_CHECK_PRINTF, PF_REAL_VFPRINTF,
  PF_MUSL_VFPRINTF.
split; [|split; [|split]].
- apply SRy.rw_of_ro; [snp_c1t HAR AG | vm_compute; reflexivity].
- snp_c8t HAR AG.
- snp_c1t HAR AG.
- snp_c8t HAR AG.
Qed.

(* printf_common's cells (I_pchead.v pctx = R_m2s.v m2s_cells /\ I_pcrr.v pcells) *)
Lemma snp_pctx : forall ly S Hp (W : world tfibsegs) mem md R (m' : word -> option byte),
  ARx ly S Hp W mem md -> snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_pchead.pctx m'.
Proof.
intros ly S Hp W mem md R m' HAR AG.
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_pchead.pctx, BzR.m2s_cells,
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_pcrr.pcells,
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.Shadow.SHB, BzR.kHighMemEnd.
split; [split; [|split]|split].
- apply SRy.rw_of_ro; [|vm_compute; reflexivity].
  apply SRy.cells_cons8; [snp_c8t HAR AG|]. apply SRy.cells_cons8; [snp_c8t HAR AG|].
  apply SRy.cells_cons8; [snp_c8t HAR AG|]. snp_c8t HAR AG.
- apply SRy.rw_of_ro; [snp_c8t HAR AG | vm_compute; reflexivity].
- apply SRy.rw_of_ro; [|vm_compute; reflexivity].
  apply SRy.cells_cons8; [snp_c8t HAR AG|]. apply SRy.cells_cons8; [snp_c8t HAR AG|]. snp_c8t HAR AG.
- snp_c8t HAR AG.
- snp_c8t HAR AG.
Qed.

(* ---- READY below the per-call store's window: FMgxaSeamReadyX's clauses (:814-1051) with their munch premise
   (a munch over vfprintf's footprint AT the harness's sp) replaced by the two facts the clauses read of it, the
   image's data and the shadow kept.  The seam inside ___interceptor_snprintf runs 2608 bytes below the harness's
   sp, under stores that earlier munches over the whole window [lo, q) reached, so the footprint form does not
   apply there. ---- *)
Lemma snp_agree_mrestrict : forall ly R (W : world tfibsegs) mem (m' : word -> option byte),
  snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> SRy.data_agree (mrestrict (w_H W) mem) m'.
Proof.
intros ly R W mem m' AG x Hx. rewrite (AG x Hx), (snp_keep_img ly R W mem x Hx).
unfold SBa.cjstore, mrestrict. destruct (w_H W x); reflexivity.
Qed.

(* FMgxaSeamReadyX.seam_copy_of_rng *)
Lemma snp_copy_of_rng : forall ly R S Hp (W : world tfibsegs) mem md (lo : Z) (m' : word -> option byte),
  ARx ly S Hp W mem md -> ly_stk_lo ly <= lo ->
  snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= ly_stk_hi ly -> 0 <= N ->
    (N = 0 \/ Dst + N <= sp - 64 - GCC.COPY_DEPTH \/ sp - 64 <= Dst) ->
    AF.pf_rng (NM.cjnormv ly R (w_H W) mem) Dst N -> (0 < N -> NM.sd_hull_kept ly R Dst N) ->
    (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) Dst N) ->
    AF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> (0 < N -> NM.sd_hull_kept ly R P N) ->
    (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N) ->
    GM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S Hp W mem md lo m' HAR Hlo AG MK sp Dst P N H1 H2 HN SEP PD KD VD PP KP VP.
pose proof (FMgxaSeamNormX.stk_bounds_x ARx LAY ly S Hp W mem md HAR) as SK0.
destruct (SRy.cells_of_agree B ARx hl LAWS TB ly S Hp W mem md m' HAR (snp_agree_mrestrict ly R W mem m' AG))
  as (C1 & C2 & _).
apply (SRy.copy_ready_intro_loc m' (sp - 64) Dst P N N N).
- unfold BzR.kHighShadowEnd, GCC.COPY_DEPTH. unfold GCA.OUT_DEPTH in H1. unfold kHighMemBeg in SK0. lia.
- unfold kHighMemEnd in SK0. lia.
- exact HN.
- unfold GCC.COPY_DEPTH in SEP |- *. lia.
- exact (AF.pf_rng_kept _ _ Dst N PD MK).
- exact (AF.pf_rng_kept _ _ P N PP MK).
- lia.
- lia.
- intros Hn0. exact (SRy.hull_kept_v ly R (w_H W) mem m' Dst N MK (KD Hn0) Hn0 (SRy.pf_rng_app _ Dst N PD) (VD Hn0)).
- intros Hn0. exact (SRy.hull_kept_v ly R (w_H W) mem m' P N MK (KP Hn0) Hn0 (SRy.pf_rng_app _ P N PP) (VP Hn0)).
- exact C1.
- exact C2.
Qed.

(* FMgxaSeamReadyX.seam_ready_set: memset inside the stack window [lo, qw) *)
Lemma snp_set_ready : forall ly R S Hp (W : world tfibsegs) mem md (lo qw : Z) (m' : word -> option byte),
  ARx ly S Hp W mem md -> ly_stk_lo ly <= lo -> qw <= ly_stk_hi ly -> NM.sd_hull_kept ly R lo (qw - lo) ->
  snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst N, lo + GSC.SET_DEPTH <= sp -> sp <= Dst -> Dst + N + 9 <= qw -> GM.set_ready m' sp Dst N.
Proof.
intros ly R S Hp W mem md lo qw m' HAR Hlo Hqw KW AG MK sp Dst N H1 H2 H3.
pose proof (FMgxaSeamNormX.stk_bounds_x ARx LAY ly S Hp W mem md HAR) as SK0.
destruct (SRy.cells_of_agree B ARx hl LAWS TB ly S Hp W mem md m' HAR (snp_agree_mrestrict ly R W mem m' AG))
  as (C1 & _ & C3 & _).
unfold GSC.SET_DEPTH in *.
destruct (Z_le_gt_dec 0 N) as [HN|HN]; [|intros HN'; lia].
destruct (SRy.stack_rng_v B ARx hl LAWS LAY ly R S Hp W mem md lo qw Dst N HAR KW Hlo ltac:(lia) HN ltac:(lia)
            ltac:(lia)) as (PD & KD & VD).
refine (SRy.set_ready_intro_cjnormv ly R (w_H W) mem m' sp Dst N N MK _ _ HN _ _ _ _ KD VD C1 C3).
- unfold BzR.kHighShadowEnd, SRy.GSC.SET_DEPTH. unfold kHighMemBeg in SK0. lia.
- unfold kHighMemEnd in SK0. lia.
- right; right. exact H2.
- exact (proj1 (NM.pf_rng_cjnormv_back ly R (w_H W) mem Dst N PD)).
- exact (proj2 (NM.pf_rng_cjnormv_back ly R (w_H W) mem Dst N PD)).
- lia.
Qed.

(* FMgxaSeamReadyX.seam_ready_strn, the hull from W_H8 (hull_of_pf_rng_H8) *)
Lemma snp_strn_ready : forall ly R S Hp (W : world tfibsegs) mem md (lo : Z) (m' : word -> option byte),
  ARx ly S Hp W mem md -> ly_stk_lo ly <= lo ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp S0 N L buf, lo + GNC.STRN_DEPTH <= sp -> sp <= ly_stk_hi ly ->
    AF.pf_rng (NM.cjnormv ly R (w_H W) mem) S0 L -> Z.min (BSF.strnlen_res N buf + 1) N <= L ->
    GC.strn_ready m' sp S0 N buf.
Proof.
intros ly R S Hp W mem md lo m' HAR Hlo HVR AG MK sp S0 N L buf H1 H2 PR HL.
pose proof (FMgxaSeamNormX.stk_bounds_x ARx LAY ly S Hp W mem md HAR) as SK0.
destruct (SRy.cells_of_agree B ARx hl LAWS TB ly S Hp W mem md m' HAR (snp_agree_mrestrict ly R W mem m' AG))
  as (C1 & _ & _ & C4 & C5 & C6).
destruct (NM.pf_rng_cjnormv_back ly R (w_H W) mem S0 L PR) as [PR0 KS].
refine (SRy.strn_ready_intro_loc m' sp S0 N L buf _ _ (AF.pf_rng_kept _ _ S0 L PR MK) HL _ C1 C4 C5 C6).
- unfold BzR.kHighShadowEnd. unfold GNC.STRN_DEPTH in H1. unfold SRy.GNC.STRN_DEPTH. unfold kHighMemBeg in SK0. lia.
- unfold kHighMemEnd in SK0. lia.
- intros Hk.
  apply (SRy.hull_kept_v ly R (w_H W) mem m' S0 _ MK
           (NM.sd_hull_kept_sub ly R S0 L S0 (Z.min (BSF.strnlen_res N buf + 1) N)
              (NM.hull_of_sh_kept ly R S0 L KS ltac:(lia) (SRy.pf_rng_app _ S0 L PR0))
              ltac:(lia) ltac:(lia) ltac:(lia))
           Hk).
  + exact (AF.app_ivl_sub S0 (S0 + L) S0 (S0 + Z.min (BSF.strnlen_res N buf + 1) N)
             (SRy.pf_rng_app _ S0 L PR0) ltac:(lia) ltac:(lia)).
  + apply (SRy.hull_prefix _ S0 L _
             (SRy.hull_of_pf_rng_H8 ARx LAY BANDP W_H8 ly R S Hp W mem md S0 L HAR HVR PR ltac:(lia))). lia.
Qed.

(* FMgxaSeamReadyX.seam_ready_copy_hull at the seam's sp Q inside the window [lo, qw), the source hull from W_H8 *)
Lemma snp_copy_ready : forall ly R S Hp (W : world tfibsegs) mem md (lo qw Q D : Z) (dn : nat)
    (m' : word -> option byte),
  ARx ly S Hp W mem md -> ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= Q - 368 -> Q <= qw -> qw <= ly_stk_hi ly ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  NM.sd_hull_kept ly R lo (qw - lo) -> NM.sd_hull_kept ly R D (Z.of_nat dn) ->
  AF.pf_rng (NM.cjnormv ly R (w_H W) mem) D (Z.of_nat dn) ->
  (0 < Z.of_nat dn -> shadow_hull_vis (aview tfibsegs (w_H W) mem) D (Z.of_nat dn)) ->
  (D + Z.of_nat dn <= lo \/ Q <= D) ->
  snp_img_agree (NM.cjnormv ly R (w_H W) mem) m' -> AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= Q - 368 ->
    (D <= Dst /\ Dst + N <= D + Z.of_nat dn \/ Q - 352 <= Dst /\ Dst + N <= Q - 352 + GXI.SNF_CAP) ->
    0 <= N ->
    (P = Q - 352 /\ N <= GXI.SNF_CAP \/ sp <= P /\ P + N + 8 <= Q - 368 \/
     AF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N) ->
    GM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S Hp W mem md lo qw Q D dn m' HAR Hlo HGEO HQ Hqw HVR KW KDD PDD VDD HSEP AG MK
  sp Dst P N H1 H2 HDst HN HP.
assert (DR : AF.pf_rng (NM.cjnormv ly R (w_H W) mem) Dst N /\ (0 < N -> NM.sd_hull_kept ly R Dst N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) Dst N) /\
             (N = 0 \/ Dst + N <= sp - 64 - GCC.COPY_DEPTH \/ sp - 64 <= Dst)).
{ destruct HDst as [[HD1 HD2]|[HD1 HD2]].
  - split; [|split; [|split]].
    + replace Dst with (D + (Dst - D)) by lia.
      exact (AF.pf_rng_sub _ D (Z.of_nat dn) (Dst - D) N PDD ltac:(lia) HN ltac:(lia)).
    + intros Hn0. exact (NM.sd_hull_kept_sub ly R D (Z.of_nat dn) Dst N KDD HD1 Hn0 ltac:(lia)).
    + intros Hn0. exact (SRy.hull_sub _ D (Z.of_nat dn) Dst N (VDD ltac:(lia)) HD1 Hn0 HD2).
    + unfold GCA.OUT_DEPTH, GCC.COPY_DEPTH in *. lia.
  - unfold GXI.SNF_CAP, GCA.OUT_DEPTH in *.
    destruct (SRy.stack_rng_v B ARx hl LAWS LAY ly R S Hp W mem md lo qw Dst N HAR KW Hlo ltac:(lia) HN ltac:(lia)
                ltac:(lia)) as (PD & KD & VD).
    split; [exact PD|]. split; [exact KD|]. split; [exact VD | lia]. }
destruct DR as (PD & KD & VD & SEP).
assert (PR : AF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N /\ (0 < N -> NM.sd_hull_kept ly R P N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N)).
{ destruct HP as [[-> HP]|[[HP1 HP2]|HP]].
  - unfold GXI.SNF_CAP, GCA.OUT_DEPTH in *.
    exact (SRy.stack_rng_v B ARx hl LAWS LAY ly R S Hp W mem md lo qw (Q - 352) N HAR KW Hlo ltac:(lia) HN
             ltac:(lia) ltac:(lia)).
  - unfold GCA.OUT_DEPTH in *.
    exact (SRy.stack_rng_v B ARx hl LAWS LAY ly R S Hp W mem md lo qw P N HAR KW Hlo ltac:(lia) HN ltac:(lia)
             ltac:(lia)).
  - split; [exact HP|]. split.
    + intros Hn0.
      exact (NM.hull_of_sh_kept ly R P N (proj2 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP))
               Hn0 (SRy.pf_rng_app _ P N (proj1 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP)))).
    + intros Hn0. exact (SRy.hull_of_pf_rng_H8 ARx LAY BANDP W_H8 ly R S Hp W mem md P N HAR HVR HP Hn0). }
destruct PR as (PP & KP & VP).
exact (snp_copy_of_rng ly R S Hp W mem md lo m' HAR Hlo AG MK sp Dst P N H1 ltac:(lia) HN SEP PD KD VD PP KP VP).
Qed.

(* FMgxaSeamReadyX.seam_ready_holds_at for a seam at sp Q inside the window [lo, qw) that R carves out, at any store
   m1 that keeps the per-call store's image data and shadow *)
Lemma snp_seam_ready : forall ly R S Hp (W : world tfibsegs) mem md (lo qw Q Fp CK D : Z) (dn : nat)
    (m1 : word -> option byte),
  ARx ly S Hp W mem md ->
  In (D, Z.of_nat dn) R -> In (lo, qw - lo) R ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= Q - 368 -> Q <= qw -> qw <= ly_stk_hi ly ->
  0x5fb000 <= Fp -> 0x5fb000 <= CK -> 0x5fb000 <= D ->
  AF.pf_rng (SBa.cjstore (w_H W) mem) D (Z.of_nat dn) ->
  (D + Z.of_nat dn <= lo \/ Q <= D) ->
  (forall x : word, bv_unsigned x < 0x5fb000 -> m1 x = NM.cjnormv ly R (w_H W) mem x) ->
  AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m1 ->
  SGd.seam_calls_ready GM.copy_ready GM.set_ready GC.strn_ready m1 Q lo Fp CK D dn.
Proof.
intros ly R S Hp W mem md lo qw Q Fp CK D dn m1 HAR InD InW HVR Hlo HGEO HQ Hqw HFp HCK HD PD0 HSEP AG1 MK1.
pose proof (FMgxaSeamNormX.stk_bounds_x ARx LAY ly S Hp W mem md HAR) as SK0.
pose proof PD0 as (_ & (HD0 & _ & HDE & _) & _).
assert (HV : shadow_hull_vis (aview tfibsegs (w_H W) mem) D (Z.of_nat dn))
  by exact (proj1 (Forall_forall _ _) HVR (D, Z.of_nat dn) InD).
assert (KDD : NM.sd_hull_kept ly R D (Z.of_nat dn))
  by (apply (NM.hull_kept_carved ly R (D, Z.of_nat dn) InD); cbn [fst snd]; lia).
assert (KW : NM.sd_hull_kept ly R lo (qw - lo)).
{ apply (NM.hull_kept_carved ly R (lo, qw - lo) InW); cbn [fst snd].
  - unfold kHighMemBeg in SK0. lia.
  - unfold AF.APPMEM_END. unfold kHighMemEnd in SK0. lia. }
assert (PDD : AF.pf_rng (NM.cjnormv ly R (w_H W) mem) D (Z.of_nat dn))
  by exact (NM.pf_rng_cjnormv ly R (w_H W) mem D (Z.of_nat dn) (NM.sh_kept_of_hull ly R D (Z.of_nat dn) KDD) PD0).
assert (MK10 : AF.meta_kept m1 (NM.cjnormv ly R (w_H W) mem)) by (intros a Ha; symmetry; exact (MK1 a Ha)).
unfold SGd.seam_calls_ready. intros m' MU _ MK.
assert (AG : snp_img_agree (NM.cjnormv ly R (w_H W) mem) m').
{ intros x Hx. rewrite <- (AG1 x ltac:(lia)). apply MU.
  unfold SGd.GV.vf_snf_fp. cbn [CJF.outside]. unfold kHighMemBeg in SK0.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
pose proof (AF.meta_kept_trans _ _ _ MK1 MK) as MK0.
split; [|split].
- intros sp Dst P N H1 H2 HDst HN HP.
  apply (snp_copy_ready ly R S Hp W mem md lo qw Q D dn m' HAR Hlo HGEO HQ Hqw HVR KW KDD PDD (fun _ => HV) HSEP
           AG MK0 sp Dst P N H1 H2 HDst HN).
  destruct HP as [HP|[HP|HP]]; [left; exact HP | right; left; exact HP |].
  right; right. exact (AF.pf_rng_kept _ _ P N HP MK10).
- intros sp Dst N H1 H2 H3.
  exact (snp_set_ready ly R S Hp W mem md lo qw m' HAR Hlo Hqw KW AG MK0 sp Dst N H1 H2 ltac:(lia)).
- intros sp S0 N L buf H1 H2 PR HL.
  exact (snp_strn_ready ly R S Hp W mem md lo m' HAR Hlo HVR AG MK0 sp S0 N L buf H1 ltac:(lia)
           (AF.pf_rng_kept _ _ S0 L PR MK10) HL).
Qed.

(* the destination's pf_rng from the contract's facts: amem_range d (n + 7) bounds the 7 bytes past each byte *)
Lemma snp_dest_rng : forall H mem D n (dn : nat),
  0 <= D -> 1 <= Z.of_nat dn <= n -> n < 2 ^ 31 -> amem_range D (n + 7) ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF D n ->
  AF.pf_rng (SBa.cjstore H mem) D (Z.of_nat dn).
Proof.
intros H mem D n dn HD0 Hdn Hn HAM7 HRA.
unfold AF.pf_rng, AF.end_in_app.
split; [lia|].
split.
{ apply (FMgxaSeamShadow.addressable_of_view H mem D (Z.of_nat dn) HD0 ltac:(lia)).
  - unfold amem_range in *. lia.
  - intros x Hx. apply HRA. lia. }
split.
- right. exact (FMgxaSeamShadow.app_mem_of_amem_range D (n + 7) (D + Z.of_nat dn) HAM7 HD0 ltac:(lia) ltac:(lia)).
- intros i Hi. exact (FMgxaSeamShadow.app_mem_of_amem_range D (n + 7) (D + i + 7) HAM7 HD0 ltac:(lia) ltac:(lia)).
Qed.

(* a munch over ranges at or above the image's top keeps every byte below it *)
Lemma snp_low_kept : forall (Wl : list (Z * Z)) (m m' : word -> option byte),
  CJF.munch Wl m m' -> Forall (fun r => 0x5fb000 <= fst r) Wl ->
  forall x : word, bv_unsigned x < 0x5fb000 -> m' x = m x.
Proof.
intros Wl m m' MU HF x Hx. apply MU. clear MU. induction HF as [|[a b] l Ha HF' IH]; [exact I|].
cbn [fst] in Ha. cbn [CJF.outside]. split; [lia | exact IH].
Qed.

(* ---- RDY: the chain's readiness at the normalized store (RT_pf_stmt.v icpt_ready at the snprintf instance) ---- *)
Lemma snp_rdy : forall ly S Hp (W : world tfibsegs) mem md (R : list (Z * Z)) (q lo d n f : Z) (dn : nat)
    (s : list Z) (v rT : Z) (a3 a4 a5 a6 a7 : word),
  ARx ly S Hp W mem md ->
  ly_stk_lo ly + 12288 <= q -> q <= ly_stk_hi ly -> q mod 16 = 0 -> lo = q - 8208 ->
  In (d, Z.of_nat dn) R -> In (lo, q - lo) R -> In (f, 7) R -> In (@RStep.sym RT_IImgA.A_img 0x1029e, 9) R ->
  In (bv_unsigned a3, Z.of_nat (length s) + 1) R ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  0x5fb000 <= d -> (d + Z.of_nat dn <= lo \/ q <= d) ->
  1 <= n < 2 ^ 31 -> Z.of_nat dn = Z.min rT (n - 1) + 1 -> 0 <= rT ->
  amem_range d (n + 7) -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n ->
  AF.pf_rng (SBa.cjstore (w_H W) mem) f 7 -> f + 7 <= 0x9e658 ->
  AF.pf_rng (SBa.cjstore (w_H W) mem) (bv_unsigned a3) (Z.of_nat (length s) + 1) ->
  (forall qpc (m' : word -> option byte), 0x5fb000 + PF_PCOM_DEPTH <= qpc -> qpc <= q - PF_SPILL ->
     (forall x : word, bv_unsigned x < 0x5fb000 -> m' x = NM.cjnormv ly R (w_H W) mem x) ->
     AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
     G_pop_arg.va_area m' (q - PF_SPILL) ([a3; a4; a5; a6; a7] ++ []) ->
     RT_pf_bz.pcom_pre f (q - PF_SPILL) qpc m') ->
  PS.icpt_ready GM.set_ready (PS.vf_ready_icpt VFB_GUARD) (NM.cjnormv ly R (w_H W) mem) q lo
    (q - PF_SNF_FRAME - PF_VSN_FRAME) d n f (q - PF_SPILL) dn (snp_fmtb ++ [0]) ([a3; a4; a5; a6; a7] ++ [])
    [PM.PA_s s; PM.PA_i v] rT.
Proof.
intros ly S Hp W mem md R q lo d n f dn s v rT a3 a4 a5 a6 a7 HAR Hstk HShi H16 Elo InD InW InF InP InS HVR
  Hdlo HSEP Hn HDN HrT HAM7 HRA PF HF PS PCOMG.
pose proof (FMgxaSeamNormX.stk_bounds_x ARx LAY ly S Hp W mem md HAR) as [SK1 SK2].
unfold kHighMemBeg, kHighMemEnd in SK1, SK2.
subst lo.
unfold PF_SNF_FRAME, PF_VSN_FRAME, PF_SPILL, PF_PCOM_DEPTH in *.
(* the per-call store's facts: the destination, the format, the %s string, musl's prefix *)
assert (PD : AF.pf_rng (SBa.cjstore (w_H W) mem) d (Z.of_nat dn))
  by (apply (snp_dest_rng _ mem d n dn); first [assumption | lia]).
assert (HVD : shadow_hull_vis (aview tfibsegs (w_H W) mem) d (Z.of_nat dn))
  by exact (proj1 (Forall_forall _ _) HVR (d, Z.of_nat dn) InD).
pose proof PD as (_ & (_ & _ & HDE & _) & _).
assert (KD : NM.sd_hull_kept ly R d (Z.of_nat dn))
  by (apply (NM.hull_kept_carved ly R (d, Z.of_nat dn) InD); cbn [fst snd]; lia).
assert (PD0 : AF.pf_rng (NM.cjnormv ly R (w_H W) mem) d (Z.of_nat dn))
  by exact (NM.pf_rng_cjnormv ly R (w_H W) mem d (Z.of_nat dn) (NM.sh_kept_of_hull ly R d (Z.of_nat dn) KD) PD).
pose proof PF as (_ & (HF0 & _ & HFE & _) & _).
assert (PF0 : AF.pf_rng (NM.cjnormv ly R (w_H W) mem) f 7).
{ apply (NM.pf_rng_cjnormv ly R (w_H W) mem f 7); [|exact PF].
  apply NM.sh_kept_of_hull. apply (NM.hull_kept_carved ly R (f, 7) InF); cbn [fst snd]; lia. }
pose proof PS as (_ & (HS0 & _ & HSE & _) & _).
assert (PS0 : AF.pf_rng (NM.cjnormv ly R (w_H W) mem) (bv_unsigned a3) (Z.of_nat (length s) + 1)).
{ apply (NM.pf_rng_cjnormv ly R (w_H W) mem _ _); [|exact PS].
  apply NM.sh_kept_of_hull. apply (NM.hull_kept_carved ly R (_, _) InS); cbn [fst snd]; lia. }
assert (PRE0 : AF.musl_prefix_addressable (NM.cjnormv ly R (w_H W) mem)).
{ apply NM.musl_prefix_cjnormv.
  - apply NM.sh_kept_of_hull. apply (NM.hull_kept_carved ly R (_, 9) InP); cbn [fst snd];
      rewrite FMgxaSeamShadow.sym_musl_prefix; unfold AF.APPMEM_END; lia.
  - exact (ShX.musl_prefix_of_ARx B ARx hl LAWS ly S Hp W mem md (FMgxaSeamShadow.zsh_rodata_of_tfib B TB) HAR). }
assert (KW : NM.sd_hull_kept ly R (q - 8208) (q - (q - 8208))).
{ apply (NM.hull_kept_carved ly R (_, _) InW); cbn [fst snd]; unfold AF.APPMEM_END; lia. }
assert (AD : AF.app_ivl d (d + Z.of_nat dn)) by exact (SRy.pf_rng_app _ d (Z.of_nat dn) PD).
assert (EV : PS.VFI_DEPTH = 5648) by reflexivity.
assert (S22 : @RStep.sym RT_IImgA.A_img 0x22e18 = 0x9e658) by (vm_compute; reflexivity).
assert (EKH : BzR.kHighShadowEnd = 0x10007fff7fff) by reflexivity.
(* the stores the chain reaches, each by munches on the stack window and the destination *)
unfold PS.icpt_ready. intros m1 MU1 _.
assert (L1 : forall x : word, bv_unsigned x < 0x5fb000 -> m1 x = NM.cjnormv ly R (w_H W) mem x).
{ apply (snp_low_kept _ _ _ MU1). repeat constructor; cbn [fst]; lia. }
assert (K1 : AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m1).
{ apply (AF.munch_meta _ _ _ MU1). cbn [AF.all_app]. split; [|split; [exact AD | exact I]].
  apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END; lia. }
split; [|split].
- (* GXA's vsnprintf_ready at musl vsnprintf's sp *)
  unfold VFC.vsnprintf_ready. intros m2 MU2 _.
  assert (L2 : forall x : word, bv_unsigned x < 0x5fb000 -> m2 x = NM.cjnormv ly R (w_H W) mem x).
  { intros x Hx. rewrite <- (L1 x Hx). apply (snp_low_kept _ _ _ MU2); [repeat constructor; cbn [fst]; lia | exact Hx]. }
  assert (K2 : AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m2).
  { apply (AF.meta_kept_trans _ _ _ K1). apply (AF.munch_meta _ _ _ MU2). cbn [AF.all_app].
    split; [|split; [exact AD | exact I]]. apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END; lia. }
  split.
  + (* the FILE memset at musl vsnprintf's frame *)
    apply (snp_set_ready ly R S Hp W mem md (q - 8208) q m2 HAR ltac:(lia) HShi KW (fun x Hx => L2 x ltac:(lia)) K2);
      unfold GSC.SET_DEPTH; lia.
  + (* ___interceptor_vfprintf's guard *)
    unfold PS.vf_ready_icpt. rewrite EV.
    split; [lia|]. split; [rewrite EKH; lia|]. split; [lia|].
    split; [replace (q - 96 - 2160 - 304) with (q + (-160) * 16) by lia; rewrite Z_mod_plus_full; exact H16|].
    split; [exact (snp_vfi_cells ly S Hp W mem md R m2 HAR (fun x Hx => L2 x ltac:(lia)))|].
    split.
    * (* printf_common's start premise at ___interceptor_vfprintf's call *)
      intros m3 MU3 _ _ VA3. unfold PF_VF_FRAME, PF_TRYINIT in MU3 |- *.
      apply PCOMG; [lia | lia | | | exact VA3].
      -- intros x Hx. rewrite <- (L2 x Hx). apply (snp_low_kept _ _ _ MU3); [repeat constructor; cbn [fst]; lia | exact Hx].
      -- apply (AF.meta_kept_trans _ _ _ K2). apply (AF.munch_meta _ _ _ MU3). cbn [AF.all_app].
         split; [|exact I]. apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END; lia.
    * (* musl vfprintf's guard, VFB_GUARD *)
      intros m3 MU3 _. unfold PF_VF_FRAME, PF_PCOM_DEPTH in MU3 |- *.
      assert (L3 : forall x : word, bv_unsigned x < 0x5fb000 -> m3 x = NM.cjnormv ly R (w_H W) mem x).
      { intros x Hx. rewrite <- (L2 x Hx). apply (snp_low_kept _ _ _ MU3); [repeat constructor; cbn [fst]; lia | exact Hx]. }
      assert (K3 : AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m3).
      { apply (AF.meta_kept_trans _ _ _ K2). apply (AF.munch_meta _ _ _ MU3). cbn [AF.all_app].
        split; [|exact I]. apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END; lia. }
      unfold VFB_GUARD. apply SGd.vf_ready_a_holds.
      -- rewrite S22. unfold PRL.zlength. cbn [length snp_fmtb app]. lia.
      -- exact (AF.pf_rng_kept _ _ _ _ PF0 K3).
      -- exact (AF.pf_rng_kept _ _ _ _ PRE0 K3).
      -- cbn [SGd.GV.args_pf]. split; [|split; exact I].
         unfold PRL.zlength. exact (AF.pf_rng_kept _ _ _ _ PS0 K3).
      -- apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END; lia.
      -- apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END; lia.
      -- apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END; lia.
      -- exact AD.
      -- unfold SGd.GC.OUT_DEPTH. lia.
      -- apply (snp_seam_ready ly R S Hp W mem md (q - 8208) q _ _ _ d dn m3 HAR InD InW HVR);
           first [exact PD | exact L3 | exact K3 | lia | unfold GCA.OUT_DEPTH; lia].
- (* the ASan facts after REAL(vsnprintf) *)
  destruct (SRy.cells_of_agree B ARx hl LAWS TB ly S Hp W mem md m1 HAR
              (snp_agree_mrestrict ly R W mem m1 (fun x Hx => L1 x ltac:(lia)))) as (C1 & _).
  exact C1.
- replace (Z.min n (rT + 1)) with (Z.of_nat dn) by lia.
  apply (SRy.chk_ok_of_pf_rng_hull_m m1 d (Z.of_nat dn) (Z.of_nat dn) (AF.pf_rng_kept _ _ _ _ PD0 K1)); [|lia].
  exact (SRy.hull_kept_v ly R (w_H W) mem m1 d (Z.of_nat dn) K1 KD ltac:(lia) AD HVD).
Qed.

Theorem snp_xn :
  asnprintf_realizes_xn B ARx (@pa_sigma _ fr_prog_listing PB_fr WS_snprintf) FR_GOT_GUARD FR_GUARD.
Proof.
unfold asnprintf_realizes_xn.
intros ly S Hp W regs mem md d n f fmt ps args T HG HPRE Ha0 Ha1 Ha2 Hn Hd0 Hf0 HSTR HPS Eps Hflo Hfhi HSA Hdlo
  HT HTl HRD HTV HARGS HWR HAM7 HROM.
subst ps. pose proof (snp_fmt_eq fmt HPS) as Efmt. subst fmt.
destruct (snp_text_shape _ T HT) as (s & v & Eargs & ET). subst args.
destruct (HSA s eq_refl) as [Hs1 Hs2]. clear HSA.
cbn [apf_args_ok apf_arg_ok] in HARGS.
destruct HARGS as ((HsB & Hs0 & HsSTR & HsRD & HsTV & HsD) & (Hv1 & Hvm) & _).
destruct HPRE as (HPX & Hstk & HSCR).
pose proof HPX as (HAR & HRET & H16 & HSlo & HShi & _ & Hgp & Htp).
pose proof (FMgxaSeamNormX.stk_bounds_x ARx LAY ly S Hp W mem md HAR) as [SK1 SK2].
unfold kHighMemBeg, kHighMemEnd in SK1, SK2.
pose proof HRD as HRD0. pose proof HsRD as HsRD0.
destruct HWR as (Hw0 & Hw1 & Hw2 & HWB & HWAM & HWRA & HWHV).
destruct HRD as (Hr0 & Hr1 & Hr2 & HRB & HRAM & HRRA & HRHV).
destruct HsRD as (Hq0 & Hq1 & Hq2 & HQB & HQAM & HQRA & HQHV).
assert (HAM7' := HAM7). unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM7'.
set (q := spZ regs) in *.
assert (Esp : bv_unsigned (getr regs 2) = q) by reflexivity.
set (sw := bv_unsigned (getr regs 13)) in *.
assert (ESS : ESTACK = 4096) by reflexivity. rewrite ESS in *.
unfold FR_GOT_GUARD, PF_GLOBALS_TOP in *.
assert (LT : Z.of_nat (length T) = Z.of_nat (length s) + Z.of_nat (length (PFC.pf_dec v)) + 2).
{ rewrite ET, length_app. cbn [length]. rewrite length_app. cbn [length]. lia. }
set (lo := q - 8208).
assert (GLO : 0x5fb000 <= lo) by lia.
set (dn := Z.to_nat (Z.min (Z.of_nat (length T)) (n - 1) + 1)).
assert (HDN : Z.of_nat dn = Z.min (Z.of_nat (length T)) (n - 1) + 1) by (unfold dn; rewrite Z2Nat.id; lia).
set (R := [(d, Z.of_nat dn); (f, 7); (lo, q - lo); (@RStep.sym RT_IImgA.A_img 0x1029e, 9);
           (sw, Z.of_nat (length s) + 1)]).
set (m0 := NM.cjnormv ly R (w_H W) mem).
pose proof (snp_ro_agree ly S Hp W mem md HAR HROM) as HRO.
destruct HG as [HGOT [can HCAN]].
(* ---- the destination: a writable present block, kept by the normalization ---- *)
assert (WD : forall a, d <= a < d + Z.of_nat dn -> writable_at tfibsegs (SBa.cjstore (w_H W) mem) a)
  by (intros a Ha; exact (proj1 (HWB a ltac:(lia)))).
destruct (FMgxaSeamCells.rw_cells_block (w_H W) mem d dn ltac:(lia) ltac:(lia) WD
            (fun a Ha => sa_writable_aview _ _ _ (WD a Ha))) as (junkd & LJ & RD).
assert (P4 : CJS.rw_cells tfibsegs m0 d [CJC.CB dn junkd]).
{ apply NM.dest_cjnormv.
  - lia.
  - unfold TASK_SIZE. lia.
  - right. rewrite NM.globals_top_A. lia.
  - intros a Ha. apply (FMgxaSeamShadow.app_mem_of_amem_range d (n + 7) a HAM7); lia.
  - exact RD. }
(* ---- the format ---- *)
assert (P6 : CJMm.bytes_at tfibsegs m0 f (GFP.zb (snp_fmtb ++ [0]))).
{ apply NM.fmt_cjnormv; [exact HRO | rewrite NM.globals_top_A; unfold PRL.zlength; cbn; lia |].
  rewrite FMgxaSeamFam.zb_zb8. apply SBa.bytes_at_of_view; [lia | cbn [length snp_fmtb app]; lia |].
  intros i Hi. cbn [length snp_fmtb app] in Hi.
  etransitivity; [exact (proj1 HSTR i ltac:(unfold PFC.pf_bytes; cbn [length snp_fmtb map app]; lia))|].
  do 7 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. }
assert (P7 : Forall (fun c => 0 <= c < 256) (snp_fmtb ++ [0])) by (repeat constructor; lia).
assert (P8 : PM.pass1_ok (snp_fmtb ++ [0]) = true) by (vm_compute; reflexivity).
assert (P9 : CJMm.bytes_at tfibsegs m0 q (CJArr.u64s [])).
{ cbn [CJArr.u64s]. apply CJMm.bytes_at_nil. lia. }
(* ---- the arguments: the %s string at a3 (its bytes, slack and range in the image's read-only data), %d in a4 ---- *)
assert (Hstr_end : FMsnprintfShared.str_end sw s <= sw + Z.of_nat (length s) + 8 /\
                   sw + Z.of_nat (length s) + 1 <= FMsnprintfShared.str_end sw s).
{ unfold FMsnprintfShared.str_end. Z.div_mod_to_equations. lia. }
assert (P12c : GXI.args_ok lo lo 0 lo 0 d (Z.of_nat dn) (SBa.cjstore (w_H W) mem) lo q lo
                 ([getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] ++ [])
                 [PM.PA_s s; PM.PA_i v]).
{ cbn [app GXI.args_ok GXI.arg_ok]. split; [|split; [|exact I]].
  - exists (FMgxaSeamFam.str_slack (w_H W) mem sw s).
    pose proof (FMgxaSeamFam.str_slack_length (w_H W) mem sw s) as Hk.
    unfold PRL.zlength. rewrite Hk, FMgxaSeamFam.slack_len_eq. fold sw.
    split.
    { apply FMgxaSeamFam.str_bytes_of_view; [lia | lia | |].
      - intros i Hi. replace (sw + i) with (sw + Z.of_nat (Z.to_nat i)) by (rewrite Z2Nat.id; lia).
        etransitivity.
        + exact (proj1 HsSTR (Z.to_nat i) ltac:(unfold PFC.pf_bytes; rewrite length_app, length_map; cbn [length]; lia)).
        + f_equal. apply snp_nth_pf_bytes; [exact HsB | lia].
      - intros x Hx. apply HsTV. unfold FMsnprintfShared.str_end in Hx. lia. }
    split; [exact HsB|]. split; [lia|]. split; [lia|].
    split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. split; [left; lia|].
    split; [left; lia|]. left; lia.
  - split; [lia | exact Hvm]. }
assert (P12 : GXI.args_ok lo lo 0 lo 0 d (Z.of_nat dn) m0 lo q lo
                ([getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] ++ [])
                [PM.PA_s s; PM.PA_i v]).
{ apply NM.args_ok_cjnormv; [exact HRO | | | exact P12c].
  - cbn [app NM.args_task]. split; [unfold PRL.zlength, TASK_SIZE; fold sw; lia | split; exact I].
  - cbn [app NM.args_app]. split; [|split; exact I].
    intros x Hx. unfold PRL.zlength in Hx. fold sw in Hx. unfold AF.app_mem, AF.LOWMEM_END. left. lia. }
(* ---- GXA's model of "%s %d " at [PA_s s; PA_i v] is T (GX's Printf_text.printf_text_ok) ---- *)
destruct (PTx.printf_text_ok snp_fmtb [PTx.Ps; PTx.PLit 32; PTx.Pd; PTx.PLit 32] [PTx.APtr s; PTx.AInt v] T
  eq_refl ltac:(cbn; rewrite snp_pf_dec_eq, ET; reflexivity)
  ltac:(intros v0 [E0|[E0|[]]]; [discriminate E0 | injection E0 as <-; lia])
  ltac:(intros u0 [E0|[E0|[]]]; discriminate E0)
  ltac:(unfold PRL.zlength; lia) ltac:(left; unfold PRL.zlength; lia)) as (P13 & _ & _ & _).
(* ---- the stack window [lo, q): present scratch, kept ---- *)
assert (P17 : CJF.stk tfibsegs m0 lo q).
{ apply NM.stk_window_cjnormv; [rewrite NM.globals_top_A; lia | unfold TASK_SIZE; lia | |].
  - intros a Ha. unfold AF.app_mem, AF.HIGHMEM_BEG, AF.APPMEM_END. right. lia.
  - apply FMgxa_bridge.stk_of_apresent; [lia | lia |]. intros a Ha. apply HSCR. unfold ascratch_stk. lia. }
(* ---- the stack-protector cells ---- *)
assert (S22 : @RStep.sym RT_IImgA.A_img 0x22e18 = 0x9e658) by (vm_compute; reflexivity).
assert (S34 : @RStep.sym RT_IImgA.A_img 0x34288 = 0x5f94b0) by (vm_compute; reflexivity).
assert (P23 : GPAD.ssp_cells m0 (w64 can)).
{ apply NM.ssp_cells_cjnormv.
  apply (FMgxaSeamCells.ssp_cells_of_view (w_H W) mem _ _ can (w64 can) eq_refl eq_refl);
    [rewrite S22, S34; exact HGOT | rewrite S34; exact HCAN | reflexivity | |].
  - intros a Ha. rewrite S22 in Ha. apply sa_ssp_writable. left. unfold FR_GOT_GUARD. lia.
  - intros a Ha. rewrite S34 in Ha. apply sa_ssp_writable. right. unfold FR_GUARD. lia. }
assert (P24 : CJMm.mem_inv tfibsegs m0) by exact (NM.mem_inv_cjnormv ly R (w_H W) mem).
assert (P30 : d + Z.of_nat dn <= lo \/ q + 8 * PRL.zlength (@nil word) <= d).
{ assert (Z0 : PRL.zlength (@nil word) = 0) by reflexivity. rewrite Z0.
  destruct (Z_le_dec q d) as [Hq|Hq].
  - right. lia.
  - left. destruct (Z_le_dec (d + Z.of_nat dn) lo) as [Hl|Hl]; [exact Hl|exfalso].
    destruct (HWB (Z.max d (q - 12288)) ltac:(lia)) as (_ & _ & Hns). apply Hns. unfold ascratch_stk. lia. }
assert (ESNI : PS.SNI_DEPTH = 8160) by reflexivity.
assert (EKH : OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.kHighShadowEnd = 0x10007fff7fff)
  by reflexivity.
(* ---- the three store obligations: the runtime cells, printf_common's start, the chain's readiness ---- *)
assert (SNI : RT_pf_bz.sni_cells m0) by exact (snp_sni_cells ly S Hp W mem md R m0 HAR (fun x _ => eq_refl)).
(* the hulls of the ranges R carves out: the destination's and the two strings' from the contract, the stack
   window's and musl's prefix's from the laws *)
assert (Elo : lo = q - 8208) by reflexivity.
assert (HVR : Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R).
{ unfold R. repeat constructor; cbn [fst snd].
  - apply (SRy.hull_prefix _ d n); [exact (HWHV ltac:(lia)) | lia].
  - exact (HRHV ltac:(lia)).
  - exact (SRy.stack_hull B ARx hl LAWS LAY ly S Hp W mem md lo (q - lo) HAR ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (SRy.prefix_hull B ARx hl LAWS ly S Hp W mem md TB HAR).
  - exact (HQHV ltac:(lia)). }
(* the format's and the %s string's pf_rng on the harness's store *)
assert (Hf7 : f + 7 <= 0x9e658) by (change (Z.of_nat (length snp_fmtb)) with 6 in Hfhi; lia).
assert (PFf : AF.pf_rng (SBa.cjstore (w_H W) mem) f 7).
{ apply (FMgxaSeamFam.pf_rng_of_str (w_H W) mem f snp_fmtb);
    [lia | change (Z.of_nat (length snp_fmtb)) with 6; lia | | exact HRRA].
  unfold amem_range, FMsnprintfShared.str_end, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  change (Z.of_nat (length snp_fmtb)) with 6. Z.div_mod_to_equations. lia. }
assert (PFs : AF.pf_rng (SBa.cjstore (w_H W) mem) sw (Z.of_nat (length s) + 1)).
{ apply (FMgxaSeamFam.pf_rng_of_str (w_H W) mem sw s); [lia | lia | | exact HQRA].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
(* printf_common's start premise at any floor below the spill and any store that keeps the bytes below the stack
   and the shadow (RT_pf_snp_pcom.v) *)
assert (PCOMG : forall qpc (m' : word -> option byte), 0x5fb000 + PF_PCOM_DEPTH <= qpc -> qpc <= q - PF_SPILL ->
    (forall x : word, bv_unsigned x < 0x5fb000 -> m' x = NM.cjnormv ly R (w_H W) mem x) ->
    AF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
    G_pop_arg.va_area m' (q - PF_SPILL) ([getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] ++ []) ->
    RT_pf_bz.pcom_pre f (q - PF_SPILL) qpc m').
{ intros qpc m' H1 H2 L K VA.
  exact (RT_pf_snp_pcom.snp_pcom ly R W mem regs (3 * 4096) f q qpc s (getr regs 13) (getr regs 14) (getr regs 15)
           (getr regs 16) (getr regs 17) m' HRO (snp_pctx ly S Hp W mem md R m0 HAR (fun x _ => eq_refl))
           ltac:(right; left; reflexivity) ltac:(do 4 right; left; reflexivity) HSTR HRD0 Hflo Hf7 HsSTR HsRD0 Hs1 Hs2
           H1 H2 ltac:(lia) L K VA). }
assert (PCOM : forall m', CJF.munch [(q - (PF_SNF_FRAME + PF_VSN_FRAME + PF_TRYINIT), q)] m0 m' ->
    CJF.wmono tfibsegs m0 m' -> CJMm.mem_inv tfibsegs m' ->
    G_pop_arg.va_area m' (q - PF_SPILL) ([getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] ++ []) ->
    RT_pf_bz.pcom_pre f (q - PF_SPILL) (q - PF_SNF_FRAME - PF_VSN_FRAME) m').
{ intros m' MU _ _ VA.
  apply PCOMG; [unfold PF_PCOM_DEPTH, PF_SNF_FRAME, PF_VSN_FRAME; lia | unfold PF_SPILL, PF_SNF_FRAME, PF_VSN_FRAME; lia
               | | | exact VA].
  - apply (snp_low_kept _ _ _ MU). repeat constructor; cbn [fst]; unfold PF_SNF_FRAME, PF_VSN_FRAME, PF_TRYINIT; lia.
  - apply (AF.munch_meta _ _ _ MU). cbn [AF.all_app]. split; [|exact I].
    apply AF.high_stack_app; unfold AF.HIGHMEM_BEG, AF.APPMEM_END, PF_SNF_FRAME, PF_VSN_FRAME, PF_TRYINIT; lia. }
assert (RDY : PS.icpt_ready GM.set_ready (PS.vf_ready_icpt VFB_GUARD) m0 q lo (q - PF_SNF_FRAME - PF_VSN_FRAME) d n f
    (q - PF_SPILL) dn (snp_fmtb ++ [0]) ([getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] ++ [])
    [PM.PA_s s; PM.PA_i v] (Z.of_nat (length T))).
{ exact (snp_rdy ly S Hp W mem md R q lo d n f dn s v (Z.of_nat (length T)) (getr regs 13) (getr regs 14)
           (getr regs 15) (getr regs 16) (getr regs 17) HAR ltac:(lia) HShi H16 Elo
           ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) ltac:(right; left; reflexivity)
           ltac:(do 3 right; left; reflexivity) ltac:(do 4 right; left; reflexivity) HVR ltac:(lia)
           ltac:(change (PRL.zlength (@nil word)) with 0 in P30; lia) Hn HDN ltac:(lia) HAM7 HWRA PFf Hf7 PFs PCOMG). }
(* ---- the chain, at the harness's registers and FP state, on the normalized store ---- *)
pose proof (CHAIN_K (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
  (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
  (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
  (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx) (@fp_csr fx) m0
  d n f dn junkd (snp_fmtb ++ [0]) [] [PM.PA_s s; PM.PA_i v] lo (w64 can) (Z.of_nat (length T)) T) as G.
cbv zeta in G. rewrite Esp in G.
assert (ZN0 : PRL.zlength (@nil word) = 0) by reflexivity.
assert (ZF7 : PRL.zlength (snp_fmtb ++ [0]) = 7) by reflexivity.
specialize (G Ha0 Ha1 Ha2 P4 HDN P6 P7 P8 P9 ltac:(rewrite ZN0; lia) PS.snf_spill_ok_nil P12 P13
  ltac:(lia) ltac:(lia) Hn P17 ltac:(rewrite ESNI; lia) ltac:(rewrite NM.globals_top_A; lia)
  ltac:(rewrite EKH; lia) ltac:(lia) H16 P23 P24
  ltac:(rewrite NM.globals_top_A, ZF7; lia) Hflo ltac:(lia) ltac:(lia)
  ltac:(lia) P30 ltac:(right; rewrite NM.globals_top_A; lia) SNI PCOM RDY).
eapply (FMgxa_bridge.srr_of_gxa_evt AF0x.Hwx_tfa).
{ eapply sa_evt_eqv.
  - eapply NM.evt_from_norm_MS_v; [exact HRO|]. exact G.
  - split; [apply RE.xregs_eqv_sym, RE.mkR_eqv_of; reflexivity|]. repeat split. }
(* ---- the chain's keep-FP post, read back on the harness's store, is art_post_x at the same fx ---- *)
intros ms' model' (y & (st0 & HQ & HREL & HSAME) & HEQ) HSBM _.
destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                Est & MU & WM & MI & ST & SSP & DST).
assert (Rl : NG.gmem_rel tfibsegs (NM.seam_drop ly R) (ms_mem y) m0').
{ pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & Rl). subst st0. exact Rl. }
pose proof (NM.ms_from_norm_v ly R y st0 _ _ _ _ _ m0' _ HREL Est) as Ey.
pose proof (NM.munch_from_norm_v ly R (w_H W) mem _ m0' _ HRO Rl HSAME MU) as MU'.
pose proof (NM.wmono_from_norm_v ly R (w_H W) mem _ m0' HRO Rl HSAME WM) as WM'.
pose proof (NM.rw_cells_from_rel_v ly R _ m0' _ _ Rl DST) as DST'.
set (m' := ms_mem y) in *.
rewrite Ey in HEQ.
destruct ms' as [R' F' pc' svc' rv' fc'' mm ro'].
destruct HEQ as (HR & HF & HPC & HSVC & HRV & HFC & HM & HROM').
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom CJMS.MS] in HR, HF, HPC, HSVC, HRV, HFC, HM, HROM'.
subst F' pc' svc' rv' fc'' mm ro'.
assert (EPC : CJMS.ret_pc (getr regs 1) = w64 (raZ regs)) by exact (SBa.ret_pc_raZ _ HRET).
cbv beta. split; [reflexivity|].
exists R', (munrestrict (w_H W) mem m'), model'.
split.
{ rewrite (SPo.cfg_of_ms fx). unfold unrestrict.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite EPC. reflexivity. }
split.
{ pose proof (same_but_materialized_frame md model' HSBM) as (_ & Hv & Hl & _).
  apply (alx_frame _ _ _ LAWS ly S Hp W mem md (munrestrict (w_H W) mem m') model' HAR).
  - intros a Ha Hown. apply (SPo.win_view_out (w_H W) mem m' _ MU' a Ha). cbn [CJF.outside].
    split; [|split; [|exact I]].
    + intros Hin. exact (alx_stack _ _ _ LAWS ly S Hp W mem md a HAR ltac:(lia) Hown).
    + intros Hin. exact (proj1 (proj2 (HWB a ltac:(lia))) Hown).
  - exact (SPo.win_visible (w_H W) mem m' WM').
  - congruence.
  - congruence.
  - unfold eager_used. rewrite Hv, Hl. reflexivity.
  - intros a _ Hh. unfold munrestrict. cbv beta.
    match goal with |- (if ?c then _ else _) = _ => replace c with true by (symmetry; exact Hh) end.
    reflexivity.
  - (* the kept bytes (W0' kept_x): image bytes (ACeg.tfib_img_range: below 0x5fb000), so outside the chain's window -
       the stack range lies above the image and the buffer [d, d + dn) starts at or above PF_GLOBALS_TOP = 0x5fb000 *)
    intros a Ha Hk. apply (SPo.munrestrict_out (w_H W) mem m' _ (Z_to_bv 64 a) MU').
    rewrite CJMS.unsigned_lit by lia. cbn [CJF.outside].
    pose proof (ACeg.tfib_img_range a (proj1 Hk)) as HIa.
    split; [|split; [|exact I]]; intros Hin; unfold PF_GLOBALS_TOP in *; lia. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct RR as [RR|RR];
    [subst r; rewrite !sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity|]).
  subst r; rewrite !sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity. }
split; [exact HSBM|].
split.
{ split.
  - rewrite sa_getr_nz by reflexivity. rewrite <- (HR _) by reflexivity. reflexivity.
  - destruct DST' as [[CW BA] _].
    cbn [CJC.cells_wf CJC.cell_wf CJC.cells_bytes CJC.cbytes] in CW, BA.
    rewrite app_nil_r in BA. destruct CW as [CWL _].
    unfold PFC.pf_bytes. rewrite map_app. cbn [map].
    intros i Hi.
    refine (SPo.view_of_bytes_at (w_H W) mem m' d _ BA _ i Hi).
    intros a Ha. apply (sa_writable_vis W mem). apply WD. rewrite CWL in Ha. lia. }
split.
{ intros a Ha Hs Hd. apply (SPo.win_view_out (w_H W) mem m' _ MU' a Ha). cbn [CJF.outside].
  unfold ascratch_stk in Hs. split; [lia | split; [lia | exact I]]. }
split.
{ apply (SPo.win_present_off (w_H W) mem m' _ MU' WM').
  repeat (apply Forall_cons; [cbn [fst snd]; right; lia|]); apply Forall_nil. }
intros a Ha. apply (SPo.win_present_off (w_H W) mem m' _ MU' WM').
- repeat (apply Forall_cons; [cbn [fst snd]; right; lia|]); apply Forall_nil.
- exact (HSCR a Ha).
Qed.

End snp.

(* ---- the chain discharged: CHAIN_K is RT_pf_chain_k.v snprintf_chain_closed_k_seam, the keep-FP chain closed from the
   GXAK twin at the bridge's invariant FMgxaSeamCall.SEAM_INV, in VFB_GUARD's text ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable hl : Z.
Hypothesis LAWS : YCbqG.AR_laws_x tfibsegs B ARx hl.
Hypothesis LAY : forall ly S Hp (W : world tfibsegs) mem md, ARx ly S Hp W mem md -> layout_ok ly.
Hypothesis BANDP : forall ly S Hp (W : world tfibsegs) mem md a, ARx ly S Hp W mem md -> in_band_rw a ->
  w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview tfibsegs (w_H W) mem a <> None.
Hypothesis TB : TfibSyms B.
Hypothesis W_H8 : forall (W : world tfibsegs) a, in_band_rw a ->
  w_H W (Z_to_bv 64 a) = w_H W (Z_to_bv 64 (a - a mod 8)).
Hypothesis REALVSN : forall ly S Hp (W : world tfibsegs) mem md, ARx ly S Hp W mem md ->
  rdword (aview tfibsegs (w_H W) mem) PF_REAL_VSNPRINTF = Some PF_MUSL_VSNPRINTF.

Theorem snp_xn_closed :
  asnprintf_realizes_xn B ARx (@pa_sigma _ fr_prog_listing PB_fr WS_snprintf) FR_GOT_GUARD FR_GUARD.
Proof. exact (snp_xn B ARx hl LAWS LAY BANDP TB W_H8 RT_pf_chain_k.snprintf_chain_closed_k_seam REALVSN). Qed.

End closed.

(* ---- at top_x's instance ARX (W_LLVMFuzzerTestOneInput_top_x.v:189-204), as FMgxaSeamARX.v restates it verbatim
   (ARX_seam): LAWS by ARX_seam_laws (top_x's ARX_laws proof), LAY / BANDP by ARX_LAY / ARX_BANDP, TB by
   AD2l.TfibB_syms ---- *)
Section arx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Hypothesis W_H8 : forall (W : world tfibsegs) a, in_band_rw a ->
  w_H W (Z_to_bv 64 a) = w_H W (Z_to_bv 64 (a - a mod 8)).
Hypothesis REALVSN : forall ly S Hp (W : world tfibsegs) mem md, FMgxaSeamARX.ARX_seam ly S Hp W mem md ->
  rdword (aview tfibsegs (w_H W) mem) PF_REAL_VSNPRINTF = Some PF_MUSL_VSNPRINTF.

Theorem snp_xn_ARX :
  asnprintf_realizes_xn AD2l.TfibB FMgxaSeamARX.ARX_seam (@pa_sigma _ fr_prog_listing PB_fr WS_snprintf)
    FR_GOT_GUARD FR_GUARD.
Proof.
exact (snp_xn_closed AD2l.TfibB FMgxaSeamARX.ARX_seam (@YGcfNames.cf_head CfParamsReply.CfParams_reply)
         FMgxaSeamARX.ARX_seam_laws FMgxaSeamARX.ARX_LAY FMgxaSeamARX.ARX_BANDP AD2l.TfibB_syms W_H8 REALVSN).
Qed.

End arx.
