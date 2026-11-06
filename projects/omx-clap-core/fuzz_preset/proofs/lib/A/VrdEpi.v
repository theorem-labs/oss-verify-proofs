(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1213 of its 1267 lines of code are new or changed and 724 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/BTxString.v, with its module paths and module names changed; 437 of its 497 lines of code are new or changed and 1207 lines of the source are left out. *)
(* fuzz_preset, slice S5b (parse_value / parse_items), image A (asan, unstripped twin f0d2e8d4): THE SHARED EPILOGUE
   of parse_value. Lane PV-epilogue (worker a Theorem Labs lane, lane WalkAlive), from WalkPValueA's handoff
   (a Theorem Labs lane's handoff, the internal file VrdEpi-handoff.diff: its statement and its entry-state lemma, re-cut to
   five regions and closed facts).

   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).

   BUILD SET (one coherent set): a working branch 4e6e65af6e1 (record PRH_FnParse.v blob 304770f5577,
   PRH_Base 52730e74901, room invariant) + a working branch 8c691f4a3a0 (VrdPro.v blob 359e06ced8d) +
   a working branch ec8b37517c2 (VrdNum.v blob 7e7610a89d1), all on a Theorem Labs lane's ENGINE FOLD 63997a07aa6
   (YCbqG blob 83da015952b; YGcallSx 17d7d2cdbcd, YC1fPx 8549c953fad, YC80x ec48991942e), listing PAImg_prog
   0ece0b9f5a3, acceptance root f65cfdd5cac. cb type-check on base f65cfdd5cac0. First Qed (eac918c26af) was on the
   pre-fold set vnum 709572908f6 + vpro b50e4aac4a2 (YCbqG 40fc8b95138); the move changed only LAWS (HL), FFLX
   (the engine's narrower form) and the new FPRES below.
   FPRES (Section hypothesis, NOT a stand-in): the flag byte of a live fake frame is present. YGcallSx 17d7d2cdbcd
   dropped it from FFLX; at ARcf it is the FIRST conjunct of YG0dcf.v AR_flag_law_cf, proved by YG0scf.v
   AR_flag_law_ok_cf (alc_flag of AR_laws_cf).

   WHAT THE SEGMENT IS (rows of a Theorem Labs lane's disassembly, the internal file parse_value.fuzz_preset.asan.s;
   row r is at parse_value + 4 * (r - 2)):
     rows 225-227  lui / addiw / `sd a0, 0(s10)`: the frame header's retire word at F = s10;
     row  228      `beqz s2`: s2 = F >= 4096, so the side-stack arm (rows 229-240) runs;
     rows 229-237  eight `sb a0, i(s8)` with a0 = -0xb: the frame's eight shadow bytes at s8 = shadow_addr F;
     rows 238-239  `ld a0, 0x38(s2)` / `sb zero, 0(a0)`: the inline RELEASE through the flag word at F + 56
                   (YGcallSx.aj_flag_store_x);
     row  240      `j` to row 249;
     rows 249-264  `mv a0, s5`, `addi sp, s0, -0xa0`, the thirteen `ld` of ra and s0..s11 (VrdPro.vrd_saved),
                   `addi sp, sp, 0xa0`;
     row  265      `ret`.
   The whole tail is ONE symbolic run from row 225 to the `ret`, taken under aj_flag_store_x.

   WHAT IT PROVES. `vrd_epi_holds`: from the join state (vrd_epi_a's conjuncts, lib/A/VrdNum.v:303-319 at
   709572908f6), parse_value returns and the whole call meets the frozen text's caller-window post `fpostWF`, AT
   PARSE_VALUE'S ENTRY FLOAT STATE (the Section's fx, pinned with `(fx := fx)`: an unpinned fpostWF under a
   `forall fxj : FPState` binder elaborates at fxj, where its fregs_kept_x is trivial - the same trap waits in any
   statement that binds an FPState), at any post body Q, given one transfer premise (HQ) that carries the arm's answer
   across the tail's three writes (the retire word, the eight shadow bytes, the flag byte) and the frame's release.
   HQ is handed the final registers' a0 = s5, aregs_preserved, the frame list after the release (frames S0), and the
   memory outside this call's own frame, its shadow and the flag byte, unchanged.

   THE SYMBOLIC STATE (VERIFY 04:14Z speed rule: every base an atom, no chunk the run does not read, closed facts).
   Atoms 0..31 are the join's registers; atom 32 is the flag address, atoms 33..45 the thirteen spilled words. Five
   regions: the spill area [s0 - 104, s0) (read only), the header word [s10, s10 + 8), the flag word
   [s2 + 56, s2 + 64) (read only, holding atom 32), the frame's eight shadow bytes [s8, s8 + 8) and the flag byte.
   The facts are numerals only, so vm_compute runs on a closed term.

   NUMERALS: 0x37c (DERIVED: row 225's offset inside parse_value); 8, 56, 64, 104, 160, 512 (LENGTH: word, flag word
   offset, class-0 frame, spill area, parse_value's frame, the shadow of the lowest frame); 4096 (LENGTH: page);
   2 ^ 44, 2 ^ 47 (LENGTH: shadow span, address bound); atom indices 8, 18, 21, 24, 26, 32..45 (DERIVED: the
   engine's numbering). No ADDRESS literal: the entry is A_prog_sigma AS_parse_value of lib/A/PAImg_prog.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog VrdPro.
(* the re-hiding move's SRr' / wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the tail's offsets inside parse_value ---- *)
Definition VE_EPI : Z := 0x37c.   (* row 225: the join *)
Definition VE_PC : Z := A_prog_sigma AS_parse_value - A_prog_base + VE_EPI.

(* ---- the symbolic state at the join (closed terms only) ---- *)
Definition ve_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 33%nat 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34%nat 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 35%nat 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36%nat 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 37%nat 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38%nat 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 39%nat 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40%nat 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 41%nat 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42%nat 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 43%nat 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44%nat 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 45%nat 0)) ].
Definition ve_regions : smem :=
  [ YP09.mkRegion (Some 8%nat) (-104) 0 0 0 ve_saved_chunks;
    YP09.mkRegion (Some 26%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 18%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 32%nat 0))];
    YP09.mkRegion (Some 24%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 32%nat) 0 1 0 1 [] ].
Definition ve_facts : facts :=
  mkFacts [ (18%nat, mkAF 4096 (2 ^ 47) 5); (24%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 0);
            (26%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF 4096 (2 ^ 47) 0) ] [] [].
Definition ve_ss : sstate := mkSS VE_PC sr_atoms ve_regions None ve_facts.
Definition ve_SH : list shent := [].
Definition ve_Bx : sv := SLit 0.
Definition ve_Bspan : Z * Z := (0, 0).
(* the callee-saved registers the prologue spilled, in spill order (ra at sp0 - 8 .. s11 at sp0 - 104) *)
Definition ve_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* the writable windows of the state: the header word, the shadow bytes, the flag byte *)
Lemma ve_wrange : forall E a F SH fl,
  bv_unsigned (ew E 26) = F -> bv_unsigned (ew E 24) = SH -> bv_unsigned (ew E 32) = fl ->
  in_wrange E (ss_mem ve_ss) a -> (F <= a < F + 8) \/ (SH <= a < SH + 8) \/ a = fl.
Proof.
intros E a F SH fl H26 H24 H32 (r & Hr & Ha). unfold ve_ss, ve_regions in Hr. cbn [ss_mem In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
Qed.

Section c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the laws of the frame-area release rule (lib/Reusable/YGcallSx.v:138-152, aj_flag_store_x's own Section
   hypotheses), proved at ARcf by the bridge lib/Reusable/YGcallScf.v - not stand-ins *)
Context {HL : Z}.   (* AR_laws_x's head length (YCbqG.v at the engine fold), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
(* the flag byte of a live fake frame is present: the walk's symbolic state writes it, so it needs the byte as a
   writable cell. The release rule no longer reads it (YGcallSx.v blob 17d7d2cdbcd dropped it from FFLX); at ARcf it
   is the FIRST conjunct of YG0dcf.v AR_flag_law_cf, proved by YG0scf.v AR_flag_law_ok_cf (alc_flag of AR_laws_cf). *)
Hypothesis FPRES : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.

Definition ve_E (regs regs0 : bvmap 5 word) (fl : Z) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs (w64 fl :: map (getr regs0) ve_saved_regs)).

(* ---- THE STATEMENT. The premises are vrd_epi_a's conjuncts (VrdNum.v:303-319 at 709572908f6), plus the text's
   own frame bound for the 104 spilled bytes (an image fact, by computation at the instance), and the transfer
   premise HQ. ---- *)
Definition vrd_epi_stmt (d : nat) : Prop :=
  forall (fxj : YK11.FPState)
    (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world SEGS) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model)
    (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model)
    (e q v pos rv k : Z)
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  104 <= STK_parse_value d ->
  ajournal_x (SK := SK) SEGS B prh_pst ARx (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
    ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a) ->
  getr regs 8 = w64 (spZ regs0) ->
  getr regs 18 = w64 (frame_addr ly 0 pos) -> getr regs 26 = w64 (frame_addr ly 0 pos) ->
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) -> getr regs 21 = w64 rv ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs0 1) ->
  vrd_saved (rdW W mem) (spZ regs0) regs0 ->
  val_mem SEGS (rdW W mem) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
  frm_zero (@YK11.fp_csr fxj) -> fregs_kept_x fx fxj ->
  (* the arm's own answer, carried across the tail's writes (inside this call's own fake frame and its shadow,
     which in_frames ly [(0, pos)] names, and the flag byte) and the frame's release *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     getr regs' 10 = w64 rv -> aregs_preserved regs0 regs' ->
     frames (stack_free_state 0 pos S) = frames S0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_frames ly [(0, pos)] a -> a <> flag_addr ly 0 pos ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     Q ly (stack_free_state 0 pos S) Hp W regs' mem' md') ->
  SRr SEGS W (mkCfg (@YK11.mkst fxj regs (w64 (A_prog_sigma AS_parse_value + VE_EPI)) mem (YK11.seg_rom SEGS)) md)
    (fpostWF (fx := fx) B ARx SK (STK_parse_value d) e (rd_fp q v) regs0 ly0 S0 Hp0 W0 mem0 md0 Q).

(* ---- the frame's geometry, from the allocator's laws ---- *)
Lemma ve_geom : forall ly S Hp (W : world SEGS) mem md pos,
  ARx ly S Hp W mem md -> In (0, pos) (frames S) ->
  4096 <= frame_addr ly 0 pos /\ frame_addr ly 0 pos + 64 <= alloc_ceiling /\ frame_addr ly 0 pos mod 32 = 0 /\
  8 * (frame_addr ly 0 pos / 8) <= frame_addr ly 0 pos < 8 * (frame_addr ly 0 pos / 8) + 8 /\
  (frame_addr ly 0 pos + 64 <= SHADOW_OFF + frame_addr ly 0 pos / 8 \/
   SHADOW_OFF + frame_addr ly 0 pos / 8 + 8 <= frame_addr ly 0 pos) /\
  4096 <= flag_addr ly 0 pos /\ flag_addr ly 0 pos < alloc_ceiling /\
  (flag_addr ly 0 pos < frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= flag_addr ly 0 pos) /\
  (flag_addr ly 0 pos < SHADOW_OFF + frame_addr ly 0 pos / 8 \/
   SHADOW_OFF + frame_addr ly 0 pos / 8 + 8 <= flag_addr ly 0 pos) /\
  (forall o, 0 <= o < 64 -> apresent (w_H W) mem (frame_addr ly 0 pos + o)) /\
  (forall o, 0 <= o < 8 -> apresent (w_H W) mem (SHADOW_OFF + frame_addr ly 0 pos / 8 + o)) /\
  apresent (w_H W) mem (flag_addr ly 0 pos).
Proof.
intros ly S Hp W mem md pos HAR Hin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md 0 pos HAR Hin) as (Hmod & Happ & Hfpres & Hshpres).
destruct (FFLX ly S Hp W mem md 0 pos HAR Hin) as (Hflown & (Hflapp & Hflimg)).
pose proof (FPRES ly S Hp W mem md 0 pos HAR Hin) as Hflpres.
pose proof (app_addr_below_ceil _ Hflapp) as (Hfl4096 & Hflceil). unfold ASAN_CEIL in Hflceil.
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & Hsepf).
pose proof (proj1 (Forall_forall _ _) Hsepf (0, pos) Hin) as HFR. cbn [fst snd] in HFR.
assert (HFB64 : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
rewrite HFB64 in HFR, Happ, Hfpres, Hshpres. change (64 / 8) with 8 in Hshpres.
destruct HFR as (HF4096 & HFceil).
pose proof (Z.mul_div_le (frame_addr ly 0 pos) 8 ltac:(lia)) as HF8a.
pose proof (Z.div_mod (frame_addr ly 0 pos) 8 ltac:(lia)) as HF8d.
pose proof (Z.mod_pos_bound (frame_addr ly 0 pos) 8 ltac:(lia)) as HF8m.
assert (HF8 : 8 * (frame_addr ly 0 pos / 8) <= frame_addr ly 0 pos < 8 * (frame_addr ly 0 pos / 8) + 8) by lia.
assert (HSB : frame_addr ly 0 pos + 64 <= SHADOW_OFF + frame_addr ly 0 pos / 8 \/
              SHADOW_OFF + frame_addr ly 0 pos / 8 + 8 <= frame_addr ly 0 pos).
{ destruct Happ as (_ & [HLo | (HH1 & HH2)]).
  - left. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
  - right. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (HflF : flag_addr ly 0 pos < frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= flag_addr ly 0 pos).
{ destruct (Z_lt_le_dec (flag_addr ly 0 pos) (frame_addr ly 0 pos)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (flag_addr ly 0 pos) (frame_addr ly 0 pos + 64)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (Hfpres (flag_addr ly 0 pos) (conj h h2)) Hflown). }
assert (HflSH : flag_addr ly 0 pos < SHADOW_OFF + frame_addr ly 0 pos / 8 \/
                SHADOW_OFF + frame_addr ly 0 pos / 8 + 8 <= flag_addr ly 0 pos).
{ destruct (Z_lt_le_dec (flag_addr ly 0 pos) (SHADOW_OFF + frame_addr ly 0 pos / 8)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (flag_addr ly 0 pos) (SHADOW_OFF + frame_addr ly 0 pos / 8 + 8)) as [h2|h2]; [|right; exact h2].
  exfalso.
  assert (Hi : 0 <= flag_addr ly 0 pos - (SHADOW_OFF + frame_addr ly 0 pos / 8) < 8) by lia.
  pose proof (proj2 (Hshpres _ Hi)) as Hno.
  unfold shadow_addr in Hno.
  replace (SHADOW_OFF + frame_addr ly 0 pos / 8 + (flag_addr ly 0 pos - (SHADOW_OFF + frame_addr ly 0 pos / 8)))
    with (flag_addr ly 0 pos) in Hno by lia.
  exact (Hno Hflown). }
split; [lia|]. split; [lia|]. split; [exact Hmod|]. split; [exact HF8|]. split; [exact HSB|].
split; [lia|]. split; [lia|]. split; [exact HflF|]. split; [exact HflSH|].
split; [intros o Ho; exact (proj1 (Hfpres (frame_addr ly 0 pos + o) ltac:(lia)))|].
split; [intros o Ho; pose proof (proj1 (Hshpres o Ho)) as Hp'; unfold shadow_addr in Hp'; exact Hp'|].
exact Hflpres.
Qed.

(* ---- the environment's atoms ---- *)
Lemma ve_E_vals : forall regs regs0 fl,
  ew (ve_E regs regs0 fl) 3 = getr regs 3 /\ ew (ve_E regs regs0 fl) 4 = getr regs 4 /\
  ew (ve_E regs regs0 fl) 8 = getr regs 8 /\ ew (ve_E regs regs0 fl) 18 = getr regs 18 /\
  ew (ve_E regs regs0 fl) 21 = getr regs 21 /\ ew (ve_E regs regs0 fl) 24 = getr regs 24 /\
  ew (ve_E regs regs0 fl) 26 = getr regs 26 /\ ew (ve_E regs regs0 fl) 32 = w64 fl /\
  (forall j, (j < 13)%nat ->
     ew (ve_E regs regs0 fl) (33 + j) = nth j (map (getr regs0) ve_saved_regs) (Z_to_bv 64 0)).
Proof.
intros regs regs0 fl.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (ve_E regs regs0 fl) n =
               ew (Ereg regs (w64 fl :: map (getr regs0) ve_saved_regs)) n)
  by (intros n Hn; unfold ve_E; apply Eimg_low; exact Hn).
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
intros j Hj. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ (Nat.succ j)).
Qed.

(* ---- the entry symbolic state of the tail ---- *)
Lemma ve_entry : forall (fxj : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs regs0 : bvmap 5 word) (mem : word -> option byte) (md : Model) (pos : Z),
  ARx ly S Hp W mem md -> In (0, pos) (frames S) ->
  getr regs 8 = w64 (spZ regs0) ->
  getr regs 18 = w64 (frame_addr ly 0 pos) -> getr regs 26 = w64 (frame_addr ly 0 pos) ->
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) ->
  vrd_saved (rdW W mem) (spZ regs0) regs0 ->
  val_mem SEGS (rdW W mem) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
  alloc_ceiling + 104 <= spZ regs0 ->
  st_ok_pi (fx := fxj) SEGS VAL (ve_E regs regs0 (flag_addr ly 0 pos)) ve_ss
    (restrict (w_H W) (@YK11.mkst fxj regs (Z_to_bv 64 (BASE + VE_PC)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS ve_Bx ve_SH (ve_E regs regs0 (flag_addr ly 0 pos)) (rdW W mem).
Proof.
intros fxj ly S Hp W regs regs0 mem md pos HAR Hin H8 H18 H26 H24 HSAV HFLG Hlo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hcl.
destruct (ve_geom ly S Hp W mem md pos HAR Hin)
  as (HF4096 & HFceil & Hmod & HF8 & HSB & Hfl4096 & Hflceil & HflF & HflSH & HFp & HSp & HFLp).
destruct (ve_E_vals regs regs0 (flag_addr ly 0 pos)) as (E3 & E4 & E8 & E18 & E21 & E24 & E26 & E32 & EX).
rewrite restrict_mkst_fx.
set (F := frame_addr ly 0 pos) in *.
set (fl := flag_addr ly 0 pos) in *.
set (E := ve_E regs regs0 fl) in *.
assert (Hsp64 : 0 <= spZ regs0 < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (Usp : bv_unsigned (ew E 8) = spZ regs0)
  by (rewrite E8, H8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (UF : bv_unsigned (ew E 26) = F)
  by (rewrite E26, H26; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (UF18 : bv_unsigned (ew E 18) = F)
  by (rewrite E18, H18; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (USH : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8).
{ rewrite E24, H24. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. unfold SHADOW_OFF. lia. }
assert (UFL : bv_unsigned (ew E 32) = fl)
  by (rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
split.
- unfold ve_ss. apply (pa_entry_st_ok_full (fx := fxj)).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ve_regions. destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
    unfold raZ in V1.
    assert (CK : forall (j : nat) off a, (j < 13)%nat -> a = spZ regs0 + off ->
              val_mem SEGS (rdW W mem) a 8 (bv_unsigned (nth j (map (getr regs0) ve_saved_regs) (Z_to_bv 64 0))) ->
              YP09.chunk_ok SEGS E (rdW W mem) (spZ regs0) (YP09.mkChunk off (CVal 8 (SOff (33 + j) 0)))).
    { intros j off a Hj Ha Hv. subst a.
      eapply (chunk_ok_val SEGS E _ (spZ regs0) off 8 _ (bv_unsigned (nth j (map (getr regs0) ve_saved_regs) (Z_to_bv 64 0))));
      [ cbn [sv_denot]; rewrite (EX j Hj), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (nth j (map (getr regs0) ve_saved_regs) (Z_to_bv 64 0))) as Hr64;
        unfold bv_modulus in Hr64; change (2 ^ (8 * Z.of_N 8)) with (2 ^ Z.of_N 64); lia
      | cbn; lia | exact Hv ]. }
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|].
      split; [intros o Ho; exfalso; lia|].
      unfold ve_saved_chunks.
      apply Forall_cons; [exact (CK 0%nat (-8) (spZ regs0 - 8) ltac:(lia) ltac:(lia) V1)|].
      apply Forall_cons; [exact (CK 1%nat (-16) (spZ regs0 - 16) ltac:(lia) ltac:(lia) V2)|].
      apply Forall_cons; [exact (CK 2%nat (-24) (spZ regs0 - 24) ltac:(lia) ltac:(lia) V3)|].
      apply Forall_cons; [exact (CK 3%nat (-32) (spZ regs0 - 32) ltac:(lia) ltac:(lia) V4)|].
      apply Forall_cons; [exact (CK 4%nat (-40) (spZ regs0 - 40) ltac:(lia) ltac:(lia) V5)|].
      apply Forall_cons; [exact (CK 5%nat (-48) (spZ regs0 - 48) ltac:(lia) ltac:(lia) V6)|].
      apply Forall_cons; [exact (CK 6%nat (-56) (spZ regs0 - 56) ltac:(lia) ltac:(lia) V7)|].
      apply Forall_cons; [exact (CK 7%nat (-64) (spZ regs0 - 64) ltac:(lia) ltac:(lia) V8)|].
      apply Forall_cons; [exact (CK 8%nat (-72) (spZ regs0 - 72) ltac:(lia) ltac:(lia) V9)|].
      apply Forall_cons; [exact (CK 9%nat (-80) (spZ regs0 - 80) ltac:(lia) ltac:(lia) V10)|].
      apply Forall_cons; [exact (CK 10%nat (-88) (spZ regs0 - 88) ltac:(lia) ltac:(lia) V11)|].
      apply Forall_cons; [exact (CK 11%nat (-96) (spZ regs0 - 96) ltac:(lia) ltac:(lia) V12)|].
      apply Forall_cons; [exact (CK 12%nat (-104) (spZ regs0 - 104) ltac:(lia) ltac:(lia) V13)|].
      apply Forall_nil.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UF. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply apresent_writable. exact (HFp o ltac:(lia)).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UF18. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      eapply (chunk_ok_val SEGS E _ F 56 8 (SOff 32%nat 0) fl);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact HFLG].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite USH. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply apresent_writable. exact (HSp o Ho).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UFL. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (fl + o) with fl by lia. apply apresent_writable. exact HFLp.
  + apply pairwise_disjoint_of_extents. unfold ve_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, UF, UF18, USH, UFL.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ve_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UF18, USH, UF, UFL. change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold SHADOW_OFF in *.
    repeat split; try lia; exact Hmod.
- unfold sh_ok, ve_SH. apply Forall_nil.
Qed.

(* a final register of the run, read off the engine's state: getr (ms_regs ms) r becomes ew E n for the atom n the
   run left in r (the register map is a closed term, so vm_compute reads it) *)
Ltac ve_fin HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS);
    lazymatch goal with |- context [sr_get (ss_regs ?ss) r] =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned
  end.

(* ---- THE STEP: rows 225..265 in ONE run under the release rule, then the return ---- *)
Lemma vrd_epi_holds : forall d, vrd_epi_stmt d.
Proof.
intros d fxj ly0 S0 Hp0 W0 regs0 mem0 md0 ly S Hp W regs mem md e q v pos rv k Q
  H104 HJ HWIN H8 H18 H26 H24 H21 H3 H4 HRA HSAV HFLG HFRM HFRK HQ.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_stk HJ) as Hstk.
assert (Hin : In (0, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & Hhi47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlo : alloc_ceiling + 104 <= spZ regs0) by lia.
destruct (ve_geom ly S Hp W mem md pos HAR Hin)
  as (HF4096 & HFceil & Hmod & HF8 & HSB & Hfl4096 & Hflceil & HflF & HflSH & HFp & HSp & HFLp).
destruct (ve_entry fxj ly S Hp W regs regs0 mem md pos HAR Hin H8 H18 H26 H24 HSAV HFLG Hlo) as [HS SHOK].
destruct (ve_E_vals regs regs0 (flag_addr ly 0 pos)) as (E3 & E4 & E8 & E18 & E21 & E24 & E26 & E32 & EX).
assert (HEI : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (ve_E regs regs0 (flag_addr ly 0 pos)))
  by (unfold ve_E; apply Eimg_env).
assert (HFB64 : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
assert (Hsp64 : 0 <= spZ regs0 < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (UF : bv_unsigned (ew (ve_E regs regs0 (flag_addr ly 0 pos)) 26) = frame_addr ly 0 pos)
  by (rewrite E26, H26; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (USH : bv_unsigned (ew (ve_E regs regs0 (flag_addr ly 0 pos)) 24) = SHADOW_OFF + frame_addr ly 0 pos / 8).
{ rewrite E24, H24. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. unfold SHADOW_OFF. lia. }
assert (UFL : bv_unsigned (ew (ve_E regs regs0 (flag_addr ly 0 pos)) 32) = flag_addr ly 0 pos)
  by (rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* the atoms of the final registers, as the entry's registers *)
assert (G3 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 3 = getr regs0 3) by (rewrite E3; exact H3).
assert (G4 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 4 = getr regs0 4) by (rewrite E4; exact H4).
assert (G8 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 8 = getr regs0 2)
  by (rewrite E8, H8; unfold w64, spZ; apply Z_to_bv_bv_unsigned).
assert (G21 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 21 = w64 rv) by (rewrite E21; exact H21).
assert (G33 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 33 = getr regs0 1) by exact (EX 0%nat ltac:(lia)).
assert (G34 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 34 = getr regs0 8) by exact (EX 1%nat ltac:(lia)).
assert (G35 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 35 = getr regs0 9) by exact (EX 2%nat ltac:(lia)).
assert (G36 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 36 = getr regs0 18) by exact (EX 3%nat ltac:(lia)).
assert (G37 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 37 = getr regs0 19) by exact (EX 4%nat ltac:(lia)).
assert (G38 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 38 = getr regs0 20) by exact (EX 5%nat ltac:(lia)).
assert (G39 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 39 = getr regs0 21) by exact (EX 6%nat ltac:(lia)).
assert (G40 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 40 = getr regs0 22) by exact (EX 7%nat ltac:(lia)).
assert (G41 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 41 = getr regs0 23) by exact (EX 8%nat ltac:(lia)).
assert (G42 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 42 = getr regs0 24) by exact (EX 9%nat ltac:(lia)).
assert (G43 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 43 = getr regs0 25) by exact (EX 10%nat ltac:(lia)).
assert (G44 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 44 = getr regs0 26) by exact (EX 11%nat ltac:(lia)).
assert (G45 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 45 = getr regs0 27) by exact (EX 12%nat ltac:(lia)).
clear E3 E4 E8 E18 E21 E24 E26 E32 EX.
remember (ve_E regs regs0 (flag_addr ly 0 pos)) as E eqn:HE.
unfold YK0s.ret_ok in HRA.
replace (w64 (A_prog_sigma AS_parse_value + VE_EPI)) with (Z_to_bv 64 (BASE + VE_PC))
  by (unfold w64, VE_PC; f_equal; change BASE with A_prog_base; lia).
(* the run, rows 225..265: a closed term *)
let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi A_prog_listing PL_prog_A) (@pl_tw A_prog_listing PL_prog_A)
                               512%nat ve_Bx ve_Bspan ve_SH FUEL ve_ss) in
lazymatch r with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi A_prog_listing PL_prog_A) (@pl_tw A_prog_listing PL_prog_A)
                   512%nat ve_Bx ve_Bspan ve_SH FUEL ve_ss = (st', rs)) by (vm_compute; reflexivity)
end.
assert (HK : (A_LIM <= 512)%nat) by (unfold A_LIM; lia).
assert (Hstat : sh_static_ok 512 ve_Bx ve_Bspan ve_SH (ss_facts ve_ss) (ss_mem ve_ss) = true)
  by (vm_compute; reflexivity).
refine (@aj_flag_store_x fxj rc SK SEGS B prh_pst ARx _ LAWS (@pa_segs_low _ A_prog_listing PI_prog_A) ASFX FFLX SFX
  asym (@pa_wx _ A_prog_listing PI_prog_A) (clookup (@pa_tbl _ A_prog_listing PI_prog_A))
  (@pa_val _ A_prog_listing PI_prog_A) (@pa_sigma _ A_prog_listing PI_prog_A) A_prog_listing
  (@pl_tpi A_prog_listing PL_prog_A) (@pl_tw A_prog_listing PL_prog_A)
  (pa_fetch_ok (L := A_prog_listing) (PI := PI_prog_A)) (@pa_cert _ A_prog_listing PI_prog_A)
  (@pa_B_ok _ A_prog_listing PI_prog_A) A_LIM A_LIM_text (@pl_lim A_prog_listing PL_prog_A)
  (@pl_len A_prog_listing PL_prog_A) (@pl_tpi_eq A_prog_listing PL_prog_A) (@pl_tw_eq A_prog_listing PL_prog_A)
  W FUEL E 512%nat ve_Bx ve_Bspan ve_SH ve_ss _ _ _ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
  ly0 S0 Hp0 W0 mem0 md0 [] ly S Hp md k 0 pos _ HK HEI ltac:(lia) HS SHOK Hstat Hrun I HJ _ _ _ _).
- (* no shadow obligation: the tail runs no instrumented check *)
  cbn [sh_obls]. apply Forall_nil.
- (* every byte the run writes: the header word and the eight shadow bytes are this call's own frame (in_frames),
     the last is the flag byte *)
  intros a Ha.
  destruct (ve_wrange E a (frame_addr ly 0 pos) (SHADOW_OFF + frame_addr ly 0 pos / 8) (flag_addr ly 0 pos)
              UF USH UFL Ha) as [Hh|[Hs|Hf]].
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists 0, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFB64. lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists 0, pos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFB64.
    change (64 / 8) with 8. lia.
  + right. exact Hf.
- (* the flag byte is 0 at the end of the run: the last region's one chunk *)
  intros ws msr Hlen HS'.
  cbn [sh_j] in Hlen. destruct ws as [|w ws]; [|discriminate Hlen].
  cbn [extK] in HS'.
  pose proof (st_ok_mem_ok SEGS _ _ _ HS') as (_ & HRS & _).
  lazymatch type of HRS with Forall _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in HRS end.
  do 4 apply Forall_inv_tail in HRS. apply Forall_inv in HRS.
  unfold region_ok in HRS.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRS.
  destruct HRS as (_ & _ & _ & HCk). apply Forall_inv in HCk.
  destruct (HCk 0 ltac:(cbn; lia)) as (b & Hb & Hm).
  cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as Hb. subst b.
  rewrite UFL, !Z.add_0_r in Hm. rewrite Hm. f_equal; apply bv_eq; vm_compute; reflexivity.
- (* the return, and the post *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HF HFr HG.
  cbn [sh_j] in Hlen. destruct ws as [|w ws]; [|discriminate Hlen].
  cbn [extK] in HS', SHOK', HEI'.
  cbn [ms_mem mkst] in HF, HFr, HG.
  pose proof (ajx_frs HJ') as Hfrs'.
  assert (R1 : getr (ms_regs ms') 1 = getr regs0 1) by (ve_fin HS'; exact G33).
  assert (R10 : getr (ms_regs ms') 10 = w64 rv) by (ve_fin HS'; exact G21).
  assert (HAP : aregs_preserved regs0 (ms_regs ms')).
  { unfold aregs_preserved, acallee_saved. intros r Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    ve_fin HS';
    rewrite ?G3, ?G4, ?G8, ?G34, ?G35, ?G36, ?G37, ?G38, ?G39, ?G40, ?G41, ?G42, ?G43, ?G44, ?G45;
    f_equal; apply bv_eq; reflexivity. }
  eapply (paj_ret_at (fx := fxj) (L := A_prog_listing) (PL := PL_prog_A) (PI := PI_prog_A) W E _ ms' _ _ HS' eq_refl
            ltac:(vm_compute; reflexivity)).
  intros mat2.
  unfold fpostWF.
  exists fxj, ly, (stack_free_state 0 pos S), Hp, (ms_regs ms'), (ms_mem ms'). eexists. exists k.
  split; [rewrite R1, HRA; reflexivity|].
  split; [exact HFRM|]. split; [exact HFRK|].
  split; [apply (ajournal_x_materialize SEGS B prh_pst ARx LAWS (@pa_segs_low _ A_prog_listing PI_prog_A)); exact HJ'|].
  split.
  { intros a Ha Hfp. rewrite <- (HWIN a Ha Hfp). apply (aview_eq_of SEGS). apply HFr.
    rewrite unsigned_lit_small by lia. intros Hw.
    destruct (ve_wrange E a _ _ _ UF USH UFL Hw) as [Hh|[Hs|Hf]]; unfold SHADOW_OFF in *; lia. }
  split; [exact HAP|].
  apply HQ; [exact R10 | exact HAP | exact Hfrs' |].
  intros a Ha Hnf Hnfl. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia. intros Hw.
  destruct (ve_wrange E a _ _ _ UF USH UFL Hw) as [Hh|[Hs|Hf]].
  + apply Hnf. unfold in_frames. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite HFB64. lia.
  + apply Hnf. unfold in_frames. exists 0, pos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr.
    cbn [fst snd]. rewrite HFB64. change (64 / 8) with 8. lia.
  + exact (Hnfl Hf).
Qed.

(* ---- THE BUDGETED STEP (the kit's cut 7cdbb61b5fa0, PRH_FnParse.v blob f0d92dcec7e9: tparse_value_specX's post is
   fpostWFbm at YCbqGwild.wbudget CW 0, so the join's journal is at a budget WS, VrdNum.vrd_epi_a). It is
   vrd_epi_holds at the entry state with its depot moved to the join's (YCbqGwild.ajournal_xw_rebase: the journal
   reads the entry depot only in its wild conjunct), then back (YCbqGwild.ajournal_xw_unbase0, with the join
   journal's own wild conjunct ajx_wild): the tail makes no allocator call, so the budget is the join's, at any budget
   predicate P the join's WS meets. The premises are vrd_epi_stmt's with the journal at WS and P WS added. ---- *)
Lemma vrd_epi_holds_b : forall d (P : list (list Z) -> Prop) (fxj : YK11.FPState)
    (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world SEGS) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model)
    (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model)
    (e q v pos rv k : Z) (WS : list (list Z))
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  104 <= STK_parse_value d ->
  ajournal_xw (SK := SK) SEGS B prh_pst ARx (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
    ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k WS ->
  P WS ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a) ->
  getr regs 8 = w64 (spZ regs0) ->
  getr regs 18 = w64 (frame_addr ly 0 pos) -> getr regs 26 = w64 (frame_addr ly 0 pos) ->
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) -> getr regs 21 = w64 rv ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs0 1) ->
  vrd_saved (rdW W mem) (spZ regs0) regs0 ->
  val_mem SEGS (rdW W mem) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
  frm_zero (@YK11.fp_csr fxj) -> fregs_kept_x fx fxj ->
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     getr regs' 10 = w64 rv -> aregs_preserved regs0 regs' ->
     frames (stack_free_state 0 pos S) = frames S0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_frames ly [(0, pos)] a -> a <> flag_addr ly 0 pos ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     Q ly (stack_free_state 0 pos S) Hp W regs' mem' md') ->
  (* the re-hiding move: SRr' at the zone RZ_cf; fpostWFb is already at wle' (PRH_Base.v) *)
  SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxj regs (w64 (A_prog_sigma AS_parse_value + VE_EPI)) mem (YK11.seg_rom SEGS)) md)
    (fpostWFb (fx := fx) B ARx SK P (STK_parse_value d) e (rd_fp q v) regs0 ly0 S0 Hp0 W0 mem0 md0 Q).
Proof.
intros d P fxj ly0 S0 Hp0 W0 regs0 mem0 md0 ly S Hp W regs mem md e q v pos rv k WS Q
  H104 HJ HP HWIN H8 H18 H26 H24 H21 H3 H4 HRA HSAV HFLG HFRM HFRK HQ.
pose proof HJ as HJ0. apply YCbqGwild.ajournal_xw_rebase in HJ0.
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
- (* the tail runs at wle (vrd_epi_holds); lifted once to SRr' *)
  exact (SRr_SRr' SEGS YGcfRehidePost.RZ_cf _ _ _
    (vrd_epi_holds d fxj ly0 (set_depot (st_depot S) S0) Hp0 W0 regs0 mem0 md0 ly S Hp W regs mem md e q v pos rv
       k Q H104 HJ0 HWIN H8 H18 H26 H24 H21 H3 H4 HRA HSAV HFLG HFRM HFRK HQ)).
- intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Hc & HZ & HK & HJ' & HW' & HAP & HQ').
  apply (SRrG_ret SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)).
  unfold fpostWFb, YCbqGwild.fpostWF_xbR.
  exists fx', ly', S', Hp', regs', mem', md', k', WS.
  split; [exact Hc|]. split; [exact HZ|]. split; [exact HK|]. split; [exact HP|].
  (* the unbased journal is at wle; the post's is at wle' (YA0nH.wle_wle') *)
  split; [apply (ajournal_xwR_mono SEGS B prh_pst ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
                   (wle_wle' SEGS YGcfRehidePost.RZ_cf));
          exact (YCbqGwild.ajournal_xw_unbase0 (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   (st_depot S) WS HJ' (YCbqG.ajx_wild HJ))|].
  split; [exact HW'|]. split; [exact HAP | exact HQ'].
Qed.

(* ---- THE BUDGET LIFT, for every epilogue form (VrdEpiA's step, VrdEpiP's P twin, VrdTop): a caller-window post
   reached from a journal REBASED at the depot d (YCbqGwild.ajournal_xw_rebase) is the budgeted post at the entry
   state, at any budget WS the original journal's wild conjunct allows (YCbqG.ajx_wild) and any predicate P of it.
   An epilogue at a budgeted join is then: rebase the join journal, run the unbudgeted epilogue at
   set_depot (st_depot S) S0, and lift its post with this lemma (vrd_epi_holds_b above is that, inline). ---- *)
Lemma vrd_epi_unbase : forall (P : list (list Z) -> Prop) (d0 : list (list Z)) STK e FP (regs0 : bvmap 5 word)
    (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model)
    (WS : list (list Z))
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (W' : world SEGS) (c' : config),
  incl (wild_part (as_universe B) d0) (wild_part (as_universe B) (st_depot S0) ++ WS) -> P WS ->
  fpostWF (fx := fx) B ARx SK STK e FP regs0 ly0 (set_depot d0 S0) Hp0 W0 mem0 md0 Q W' c' ->
  fpostWFb (fx := fx) B ARx SK P STK e FP regs0 ly0 S0 Hp0 W0 mem0 md0 Q W' c'.
Proof.
intros P d0 STK e FP regs0 ly0 S0 Hp0 W0 mem0 md0 WS Q W' c' Hinc HP
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Hc & HZ & HK & HJ' & HW' & HAP & HQ').
unfold fpostWFb, YCbqGwild.fpostWF_xbR.
exists fx', ly', S', Hp', regs', mem', md', k', WS.
split; [exact Hc|]. split; [exact HZ|]. split; [exact HK|]. split; [exact HP|].
(* the unbased journal is at wle; fpostWFb's is at wle' (YA0nH.wle_wle') *)
split; [apply (ajournal_xwR_mono SEGS B prh_pst ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
                 (wle_wle' SEGS YGcfRehidePost.RZ_cf));
        exact (YCbqGwild.ajournal_xw_unbase0 (SK := SK) SEGS B prh_pst ARx _ _ _ _ _ Hp0 _ _ _ _ _ _ _ _ _ _ _
                 d0 WS HJ' Hinc)|].
split; [exact HW'|]. split; [exact HAP | exact HQ'].
Qed.

End c.

(* the axiom audit of the epilogue lemmas (the kit's cut re-fit, lane RValue), in the build log of record *)
Print Assumptions vrd_epi_holds.
Print Assumptions vrd_epi_holds_b.
Print Assumptions vrd_epi_unbase.
