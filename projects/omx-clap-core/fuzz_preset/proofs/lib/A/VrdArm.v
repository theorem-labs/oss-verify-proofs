(* fuzz_preset, slice S5b, lane VstrA: the STRING, CONTAINER and LITERAL arms of parse_value's dispatch
   (image A 0x85f10), as three SEGMENT statements over image A's whole-program listing, with the model side of
   PjGrammar.jr_value's matching arm proved for each. rule 24: no function is proved here, and no arm is a
   function: each takes the state the dispatch hands it, its callee's PUBLISHED contract, and the epilogue's step,
   all as named Section hypotheses.

   ROWS are the lines of the #102 pin A' image's disassembly of parse_value: line n is image A 0x85f10 + 4 * (n - 2),
   i.e. listing slot n + 4682 of lib/A/Listing_prog.v (line 4913 of that file is `PCall AS_parse_items`, line 4920
   `PCall AS_literal`, line 4839 `PCall AS_parse_string`).
   - the STRING arm, rows 135..151 (0x86124..0x86164): rows 135-138 are the shadow check of the 4-byte store,
     row 140 `sw a0, 0(s3)` writes the node's type tag 4, row 142 `jal 0x180c <parse_string>` reads the string at
     the cursor, row 143 `addi s3, s3, 0x10` moves to the node's str field, rows 144-147 check that store's
     shadow, row 148 `sd a0, 0(s3)` stores the block, rows 149-150 `snez s5, a0; addi s5, s5, -1` make the
     return code, and row 151 `j 0x128` JOINS THE EPILOGUE AT ROW 225 (0x8628c).
   - the CONTAINER arm, rows 213..217 (0x8625c..0x8626c): the array case enters at row 213 and sets a2 = 0, the
     object case enters at row 131 (0x86114) and sets a2 = 1 before jumping into row 216. Row 216
     `jal 0x1030 <parse_items>` passes the SAME cursor q and the SAME nesting d: no register carries the depth,
     parse_items reads it out of the cursor's third field and raises it itself (image A 0x87318 `lw a1, 0(s1)`,
     0x87320 `addi a2, a1, 1`, 0x87324 `sw a2, 0(s1)`, with s1 = q + 16). Row 217 `j 0x1c` JOINS THE EPILOGUE AT
     ROW 224 (0x86288, `mv s5, a0`), one row above row 225.
   - the LITERAL arm, rows 218..223 (0x86270..0x86284): the `auipc a0, 0xfff9b` / `addi a1, a0, 0x1f0` pair of
     rows 218-219 addresses "true" and row 220 sets a2 = 2; "false" is addressed by rows 119-120 with a2 = 1
     (row 118's `f` test) and "null" by rows 152-153 with a2 = 0 (row 126's `n` test); all three reach row 221,
     where a1 holds the keyword and a2 the node's tag. Row 223 `jal 0x1cdc <literal>`, and the arm FALLS THROUGH
     to ROW 224 (0x86288), JOINING THE EPILOGUE THERE.

   Every errpath_* call reachable from these rows (rows 329-374) is an ASan REPORT, unreachable under the
   premises: the walk discharges it from the shadow premises (rd_pre's range_addressable of the cursor and
   rd_node_okR's of the node). No contract is assumed for an errpath_* symbol.

   WHAT IS ASSUMED AND WHY (rule 24): the three callees are taken by their PUBLISHED texts, by name -- the kit's
   lib/A/PRH_FnReader.v (tparse_string_specX, tliteral_specX) and this slice's lib/A/PRH_FnParse.v
   (tparse_items_specX at d, the depth the call passes) -- and every arm concludes at VnumD's join state
   vrd_epi_a (lib/A/VrdNum.v). No text is restated here; the string arm's lemmas (lib/A/VrdArmStrOk.v) take
   parse_string's text, tparse_string_specX, as it is published. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
(* NOTE: lib/Reusable/YCbqGcall.v (aj_call_x) is NOT imported: at YCbqG ea24ad37a3c it does not compile
   (aj_call_x still passes ajournal_x_sub the old footprint premise). The arm proofs need it; the statements
   do not. Reported to a Theorem Labs lane 2026-10-28. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
(* YC80xf: the paj_run_xf family, whose write premise awr_ok_fr admits a store into a byte the
   footprint names inside a frame of the journal's entry state -- the string arm's stores to the node
   (rows 140 and 148) when the node lies in a CALLER's live fake frame. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdPro.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog VrdNum.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
(* the re-hiding move's SRr' / wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------- *)
(* 1. THE MODEL SIDE: which arm of PjGrammar.jr_value the first byte at the cursor selects.                  *)
(* ------------------------------------------------------------------------------------------------------- *)

Lemma vrd_skip_le : forall z, (length (PjGrammar.skip z) <= length z)%nat.
Proof.
  induction z as [|b z IH]; cbn [PjGrammar.skip length]; [lia|].
  destruct (PjGrammar.ws b); cbn [length]; lia.
Qed.

Section model.
Variable st : list Z -> Z * Z.

Lemma vrd_jrl_fuel : forall f1 f2 dd (o : bool) n cap acc y ok,
  (2 * length y + 2 <= f1)%nat -> (2 * length y + 2 <= f2)%nat ->
  PjGrammar.jrl st f1 dd o n cap acc y ok = PjGrammar.jrl st f2 dd o n cap acc y ok.
Proof.
  intros f1 f2 dd o n cap acc y ok H1 H2.
  rewrite (proj2 (PjGrammar.fuel_mono st (2 * length y + 2)) dd o n cap acc y f1 ok ltac:(lia) H1).
  symmetry.
  exact (proj2 (PjGrammar.fuel_mono st (2 * length y + 2)) dd o n cap acc y f2 ok ltac:(lia) H2).
Qed.

Lemma vrd_cont_fuel : forall f1 f2 dd (o : bool) b y ok,
  (2 * length y + 2 <= f1)%nat -> (2 * length y + 2 <= f2)%nat ->
  PjGrammar.jr_cont (PjGrammar.jrl st f1) dd o (b :: y) ok =
  PjGrammar.jr_cont (PjGrammar.jrl st f2) dd o (b :: y) ok.
Proof.
  intros f1 f2 dd o b y ok H1 H2. pose proof (vrd_skip_le y) as Hsy.
  unfold PjGrammar.jr_cont. destruct (Nat.ltb PjGrammar.MAXD (S dd)); [reflexivity|].
  cbn [List.tl]. destruct (PjGrammar.skip y) as [|c r] eqn:Ey.
  - apply vrd_jrl_fuel; cbn [length]; lia.
  - cbn [length] in Hsy.
    destruct (c =? PjGrammar.closer o); [reflexivity|].
    apply vrd_jrl_fuel; cbn [length]; lia.
Qed.

Lemma vrd_cont_model : forall d b y x ok (o : bool),
  PjGrammar.skip x = b :: y -> b = (if o then 123 else 91) ->
  PjGrammar.jr_value st d x ok = PjGrammar.jr_items st d o (b :: y) ok.
Proof.
  intros d b y x ok o Hs Hb.
  assert (Hlen : (S (length y) <= length x)%nat)
    by (pose proof (vrd_skip_le x) as H; rewrite Hs in H; cbn [length] in H; exact H).
  unfold PjGrammar.jr_value, PjGrammar.jr_items. cbn [PjGrammar.jrv]. rewrite Hs.
  destruct o; subst b.
  - rewrite Z.eqb_refl. apply vrd_cont_fuel; cbn [length]; lia.
  - replace (91 =? 123) with false by reflexivity. rewrite Z.eqb_refl.
    apply vrd_cont_fuel; cbn [length]; lia.
Qed.

Lemma vrd_str_model : forall d y x ok,
  PjGrammar.skip x = 34 :: y ->
  PjGrammar.jr_value st d x ok =
  PjGrammar.jbind (PjGrammar.jr_string y) (fun '(s, r) => PjGrammar.jret (JStr s, r)) ok.
Proof.
  intros d y x ok Hs. unfold PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite Hs. reflexivity.
Qed.

Lemma vrd_lit_model : forall d b y x ok,
  PjGrammar.skip x = b :: y ->
  (b = 116 \/ b = 102 \/ b = 110) ->
  PjGrammar.jr_value st d x ok =
  PjGrammar.lit (if b =? 116 then PjGrammar.w_true else if b =? 102 then PjGrammar.w_false
                 else PjGrammar.w_null)
                (if b =? 116 then JTrue else if b =? 102 then JFalse else JNull) (b :: y) ok.
Proof.
  intros d b y x ok Hs Hb. unfold PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite Hs.
  destruct Hb as [-> | [-> | ->]]; reflexivity.
Qed.

End model.

(* ------------------------------------------------------------------------------------------------------- *)
(* 2. THE THREE ARM SEGMENTS of parse_value, over image A's whole-program listing.                           *)
(* ------------------------------------------------------------------------------------------------------- *)

Section arms.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PI_prog_A).

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

(* ---- the call rule a CALLER-WINDOW callee needs ---- *)

(* YCbqGcall.aj_call_x composes a callee whose text ends in apost_base_x, whose journal runs at the CALL's sp.
   All three callees of these arms end in fpostW / fpostWF, whose journal runs at (STK1 + e1) (sp_call + e1):
   that is not an instance of apost_base_x at any STK, because the journal's window [sp0 - STK, sp0) moves with
   sp0. The two lemmas below are aj_call_x / aj_call_xF with the window, over the same two engine lemmas
   (YCbqG.afn_pre_x_at for the callee's entry pre, YCbqG.ajournal_x_sub for the composition).
   The caller's own journal is already in window form (vrd_live), so the callee's window top and the caller's
   journal sp0 are the SAME address: that is the premise `o + e1 = 0`, and it makes ajournal_x_sub's two numeric
   premises `sp0 <= sp0` and `STK1 - o <= STK`, the second of which is each arm's stack-budget premise. *)
Lemma vrd_call_W :
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (fpostW B ARx SK STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (* the callee's footprint, in exactly the shape YCbqG.ajournal_x_sub takes at base b816476b5f1 (four
     disjuncts, the fourth the caller's own real-stack window), passed through unchanged *)
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/
     (alloc_ceiling <= a /\ sp0 - STK <= a < sp0)) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx (STK1 + e1) sp0 FP1 lyc Sc Hpc W (ms_mem ms) mdc []
         ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 Q
HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee.
  eapply (afn_pre_x_at SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k
    (ms_regs ms) STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HWIN & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
rewrite Hsp' in HJ1, HWIN.
replace (sp0 + o + e1) with sp0 in HJ1 by zlia.
split; [| split; [exact HJ1 | split; [| split; [exact HP | exact HQ]]]].
- change own with ([] ++ own).
  eapply (ajournal_x_sub SEGS B prh_pst ARx LAWS pa_segs_low);
    [exact HJ | replace sp0 with (sp0 + o + e1) in HJ1 by zlia; exact HJ1 | zlia | zlia
    | intros a Ha; destruct (HF a Ha) as [H|[H|[H|[_ H]]]]; [left | right; left | right; right; left
      | right; right; right]; exact H].
- intros a Ha Hn. apply HWIN; [zlia | exact Hn].
Qed.

(* vrd_call_W for a CALLER-WINDOW callee that may change the floating-point state: parse_items (and
   parse_value) reach musl strtod, so their texts end in fpostWF. The continuation runs at the callee's float
   state fx', with the rounding mode back at 0 and fs0-fs11 kept; YCbqGcall.st_ok_restrict_xfx moves a symbolic
   state to it. Otherwise identical to vrd_call_W, over the same two engine lemmas. *)
Lemma vrd_call_WF :
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (fpostWF B ARx SK STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (* the callee's footprint, in exactly the shape YCbqG.ajournal_x_sub takes at base b816476b5f1 (four
     disjuncts, the fourth the caller's own real-stack window), passed through unchanged *)
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/
     (alloc_ceiling <= a /\ sp0 - STK <= a < sp0)) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx2 regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fx fx2 /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx (STK1 + e1) sp0 FP1 lyc Sc Hpc W (ms_mem ms) mdc []
         ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 Q
HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee.
  eapply (afn_pre_x_at SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k
    (ms_regs ms) STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta.
intros W2 c2 _ (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HWIN & HP & HQ).
exists fx2, ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|].
rewrite Hsp' in HJ1, HWIN.
replace (sp0 + o + e1) with sp0 in HJ1 by zlia.
split; [| split; [exact HJ1 | split; [| split; [exact HP | exact HQ]]]].
- change own with ([] ++ own).
  eapply (ajournal_x_sub SEGS B prh_pst ARx LAWS pa_segs_low);
    [exact HJ | replace sp0 with (sp0 + o + e1) in HJ1 by zlia; exact HJ1 | zlia | zlia
    | intros a Ha; destruct (HF a Ha) as [H|[H|[H|[_ H]]]]; [left | right; left | right; right; left
      | right; right; right]; exact H].
- intros a Ha Hn. apply HWIN; [zlia | exact Hn].
Qed.

(* ---- THE SAME TWO CALL RULES, CARRYING A MEMORY INVARIANT P (YSRrMemnorm's srr_inv_laws / srr_inv_call) ----
   An SRr post is opaque once Qed, so an end-state memory invariant must be in a segment's STATEMENT (the generic
   SRr_memnorm was measured NOT provable, a Theorem Labs lane). Every callee text posts in the m-form (fpostWm / fpostWFm =
   fpostW / fpostWF over fQmn mem Q), whose second conjunct is the keep `memnorm mem -> memnorm mem'`, and
   srr_inv_call carries P across that keep. These are vrd_call_W / vrd_call_WF at Q := fQmn (ms_mem ms) Q plus that
   one step; the two lemmas above are unchanged. *)
Lemma vrd_call_W_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  P (ms_mem (cfg_ms (mkCfg ms mdc))) ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (fpostWm B ARx SK STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/
     (alloc_ceiling <= a /\ sp0 - STK <= a < sp0)) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx (STK1 + e1) sp0 FP1 lyc Sc Hpc W (ms_mem ms) mdc []
         ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2 /\
       P (ms_mem (cfg_ms c2))).
Proof.
intros P _ PCALL W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch HPM Hcallee HF.
eapply SRr_mono.
{ exact (vrd_call_W W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1
    (fQmn (ms_mem ms) Q) HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch Hcallee HF). }
cbv beta.
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HJ2 & HWIN & HP & HQ & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact HJ1|]. split; [exact HJ2|]. split; [exact HWIN|]. split; [exact HP|].
split; [exact HQ|].
exact (PCALL (ms_mem ms) mem2 HK HPM).
Qed.

Lemma vrd_call_WF_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 (o : Z) raw ch1
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  P (ms_mem (cfg_ms (mkCfg ms mdc))) ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (fpostWFm B ARx SK STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/
     (alloc_ceiling <= a /\ sp0 - STK <= a < sp0)) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx2 regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fx fx2 /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_x (SK := SK) SEGS B prh_pst ARx (STK1 + e1) sp0 FP1 lyc Sc Hpc W (ms_mem ms) mdc []
         ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2 /\
       P (ms_mem (cfg_ms c2))).
Proof.
intros P _ PCALL W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1 Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch HPM Hcallee HF.
eapply SRr_mono.
{ exact (vrd_call_WF W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 e1 FP1 o raw ch1
    (fQmn (ms_mem ms) Q) HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch Hcallee HF). }
cbv beta.
intros W2 c2 _ (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HJ2 & HWIN & HP & HQ & HK).
exists fx2, ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact HJ1|]. split; [exact HJ2|].
split; [exact HWIN|]. split; [exact HP|]. split; [exact HQ|].
exact (PCALL (ms_mem ms) mem2 HK HPM).
Qed.

(* ---- THE BUDGETED TWINS (the kit's cut 7cdbb61b5fa0, PRH_FnReader.v blob f1ae32e3b2cd / PRH_FnParse.v blob f0d92dcec7e9:
   parse_string's text posts fpostWbm and parse_items' / parse_value's fpostWFbm, at YCbqGwild.wbudget CW 0, the
   journal at a budget WS1 of wild traces of which the text claims Pb WS1). vrd_call_W_P / vrd_call_WF_P with the
   caller's journal at a budget WS0 and the callee's post budgeted at Pb: the callee's entry pre by
   YCbqGwild.afn_pre_x_at_w and the composition by YCbqG.ajournal_xw_sub, whose budget is WS0 ++ WS1 - the window
   forms of the engine's YCbqGwild.aj_call_xWb / aj_call_xWFb in this file's shape (premise `o + e1 = 0`, the
   four-disjunct footprint), as a Theorem Labs lane's Tx102Glue.s10_call_Wb / s10_call_Wbm are for tx. A callee with an
   unbudgeted post (literal, grow) is the case Pb := fun ws => ws = [] through YCbqGwild.fpostW_xb_of_x /
   fpostWF_xb_of_x. The four lemmas above are unchanged.
   THE RE-HIDING MOVE: the three budgeted texts cross a free (parse_string frees its block on a bad escape,
   parse_items / parse_value free on refusal), so they conclude SRr' segs RZ_cf with their journal at wle' (fpostWbm /
   fpostWFbm are at wle', PRH_Base.v). These two rules take the callee that way, take the caller's journal at wle'
   too (a journal at wle lifts by YCbqG.ajournal_xwR_mono with YA0nH.wle_wle'), and conclude SRr' with both journals
   at wle': the engine's R forms YCbqGwild.afn_pre_x_at_wR / YCbqG.ajournal_xw_subR at R := wle' segs RZ_cf. ---- *)
Lemma vrd_call_Wb_P : forall (P : (word -> option byte) -> Prop), srr_inv_call SEGS P ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 (o : Z) raw ch1
    (Pb : list (list Z) -> Prop)
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W0 mem md own
    lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  P (ms_mem (cfg_ms (mkCfg ms mdc))) ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (fpostWbm B ARx SK Pb STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/
     (alloc_ceiling <= a /\ sp0 - STK <= a < sp0)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1 (WS1 : list (list Z)),
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\ Pb WS1 /\
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK1 + e1) sp0 FP1 lyc Sc Hpc W
         (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2 /\
       P (ms_mem (cfg_ms c2))).
Proof.
intros P PCALL W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 o raw ch1 Pb Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch HPM Hcallee HF.
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)).
{ apply Hcallee.
  eapply (YCbqGwild.afn_pre_x_at_wR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp
    W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 (ms_regs ms) STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ HN. unfold fpostWbm, fpostWb, YCbqGwild.fpostW_xbR in HN.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ1 & HWIN & HP & HQ & HK).
exists ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|]. split; [exact HPW|].
rewrite Hsp' in HJ1, HWIN.
replace (sp0 + o + e1) with sp0 in HJ1 by zlia.
split; [| split; [exact HJ1 | split; [| split; [exact HP | split; [exact HQ |]]]]].
- change own with ([] ++ own).
  eapply (ajournal_xw_subR SEGS B prh_pst ARx LAWS pa_segs_low (wle' SEGS YGcfRehidePost.RZ_cf)
            (wle'_trans SEGS YGcfRehidePost.RZ_cf));
    [exact HJ | exact HJ1 | zlia | zlia
    | intros a Ha; destruct (HF a Ha) as [H|[H|[H|[_ H]]]]; [left | right; left | right; right; left
      | right; right; right]; exact H].
- intros a Ha Hn. apply HWIN; [zlia | exact Hn].
- exact (PCALL (ms_mem ms) mem2 HK HPM).
Qed.

Lemma vrd_call_WFb_P : forall (P : (word -> option byte) -> Prop), srr_inv_call SEGS P ->
  forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 (o : Z) raw ch1
    (Pb : list (list Z) -> Prop)
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W0 mem md own
    lyc Sc Hpc W (ms_mem ms) mdc k WS0 ->
  spZ (ms_regs ms) = sp0 + o ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK -> o + e1 = 0 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  P (ms_mem (cfg_ms (mkCfg ms mdc))) ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr' SEGS YGcfRehidePost.RZ_cf W
     (mkCfg (YK11.mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (fpostWFbm B ARx SK Pb STK1 e1 FP1 (ms_regs ms) lyc Sc Hpc W (ms_mem ms) mdc Q)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (exists f, In f own /\ in_zr a (frame_rng lyc f)) \/
     (alloc_ceiling <= a /\ sp0 - STK <= a < sp0)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 (WS1 : list (list Z)),
       c2 = mkCfg (@YK11.mkst fx2 regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fx fx2 /\ Pb WS1 /\
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W0 mem md own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK1 + e1) sp0 FP1 lyc Sc Hpc W
         (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       (forall a, sp0 + o <= a < sp0 -> ~ inFP FP1 a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) /\
       aregs_preserved (ms_regs ms) regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2 /\
       P (ms_mem (cfg_ms c2))).
Proof.
intros P PCALL W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 e1 FP1 o raw ch1 Pb Q
  HS Hrv HJ Hsp' Hal Hneg Hstk1 Hbud Hoe Hgp Htp Hra Hraw Hra4 Hch HPM Hcallee HF.
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)).
{ apply Hcallee.
  eapply (YCbqGwild.afn_pre_x_at_wR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp
    W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS0 (ms_regs ms) STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ HN. unfold fpostWFbm, fpostWFb, YCbqGwild.fpostWF_xbR in HN.
destruct HN as (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HWIN & HP & HQ
  & HK).
exists fx2, ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HPW|].
rewrite Hsp' in HJ1, HWIN.
replace (sp0 + o + e1) with sp0 in HJ1 by zlia.
split; [| split; [exact HJ1 | split; [| split; [exact HP | split; [exact HQ |]]]]].
- change own with ([] ++ own).
  eapply (ajournal_xw_subR SEGS B prh_pst ARx LAWS pa_segs_low (wle' SEGS YGcfRehidePost.RZ_cf)
            (wle'_trans SEGS YGcfRehidePost.RZ_cf));
    [exact HJ | exact HJ1 | zlia | zlia
    | intros a Ha; destruct (HF a Ha) as [H|[H|[H|[_ H]]]]; [left | right; left | right; right; left
      | right; right; right]; exact H].
- intros a Ha Hn. apply HWIN; [zlia | exact Hn].
- exact (PCALL (ms_mem ms) mem2 HK HPM).
Qed.

(* the nesting of this call of parse_value, and the call contexts the texts quantify over *)
Variable d : nat.
Variable CTX : list (list Z).
(* The kit's call-graph universe closure takes the driver's contexts (PRH_Base.v prh_univ_closure B CTX0, the kit's cut
   7cdbb61b5fa0), and the cursor texts take the cursor set CW (the run-word list DW is GONE at the cut) *)
Variable CTX0 : list (list Z).
Variable CW : list (list Z).

(* ---- the callees, by their published texts (no text is restated) ---- *)

(* parse_string, the kit's text, lib/A/PRH_FnReader.v tparse_string_specX *)
Hypothesis H_parse_string : tparse_string_specX B ARx SK CTX0 CW.
(* literal, the kit's text, lib/A/PRH_FnReader.v tliteral_specX *)
Hypothesis H_literal : tliteral_specX B ARx SK.
(* parse_items AT THE DEPTH THE CALL PASSES, which is d (row 216 hands it the same cursor and no depth
   register; parse_items raises the depth itself), lib/A/PRH_FnParse.v tparse_items_specX *)
Hypothesis H_parse_items : tparse_items_specX B ARx SK d CTX CTX0 CW.

(* ---- the state the dispatch hands an arm: lane VproA's vrd_disp_a, lib/A/VrdPro.v ---- *)

(* VrdPro.vrd_disp_a is the state at the FIRST ROW of the selected arm: the arm tag comes off the first
   non-white byte (vrd_arm_of), the pc is pa_sigma AS_parse_value + vrd_arm_off arm, the journal is already at
   the caller-window stack (STK_parse_value d + e) (spZ regs0 + e) with FP = rd_fp q v and own = [(0, pos)],
   and the register map vrd_regs pins s3 = v, s4 = q, a0 = the advanced cursor p', sp = the 32-aligned frame
   spZ regs0 - 160 - (spZ regs0 - 160) mod 32. The arm lemmas (VrdArmStrOk.vrd_str_a_okP, VrdNumA.vrd_num_a_P,
   VrdArmLC's vrd_cont_aLC_P_holds / vrd_lit_aLC_P_holds) take it and add only what their own call needs.
   The stack drop from parse_value's entry sp to the dispatch sp is therefore 160 or 176, so each arm's stack
   budget is stated against 176. *)

(* ---- the epilogue step: lane VnumB's vrd_epi_a (lib/A/VrdNum.v), at ROW 225 = 0x8628c ---- *)

(* H_vrd_epi_a is RETIRED (a Theorem Labs lane, 2026-10-29 02:04Z): it lacked the frame registers (s2 / s10 / s8), the
   frame's flag word at F + 56, this call's own fake frame and rd_blocks_move, and is not provable from an
   arm's state. Every arm CONCLUDES at VnumB's vrd_epi_a (lib/A/VrdNum.v, a working branch 88c78d5e972),
   whose RQ is VnumB's vrd_pv_post -- the body of tparse_value_specX d's post with the return value rv in
   place of `getr regs' 10`, no registers at all (the shared tail reloads them), and rd_blocks_move's frames
   clause read AT THE JOIN, where this call's own frame (0, pos) is still live. The step from the join to
   tparse_value_specX's post is the epilogue lane's (rows 225..265). *)

(* ========================================================================================================= *)
(* LANE VstrB: THE PROOF OF THE STRING ARM (rows 135..151, joining the epilogue at ROW 225).                   *)
(* ========================================================================================================= *)

(* THE ARM LEMMAS ARE IN lib/A/VrdArmStrOk.v (vrd_str_a_okP, generic in a memory invariant P, and vrd_str_a_ok, its
   corollary at P := fun _ => True), the post-call half in lib/A/VrdArmStr.v (vrs_join and the lemmas it rests on);
   this file keeps the call rules and the toolkit below, which they cite. What the arm lemmas carry beyond fpre and
   vrd_disp_a, each named in their statements:
   - `HL = cf_head`: AR_laws_x's field 14 (alx_hshadow) at the instance's head length; an identity at the cf
     instance. It rebuilds the node's range_addressable after the call when the node lies in a harness block.
   - `8 <= cf_head`: prh_hblock reads the hidden head as a WORD at a - cf_head (ASK cf_head_wide, a Theorem Labs lane).
   - `forall a, Exists (in_zr a) prh_pst -> in_img SEGS a`: the image fact S1ImgA.pst_in_img_A (this Section is
     generic in PrhImg).
   - `pi_s0cur F_parse_string = Some 0` and `pi_s0cur F_parse_items = Some 0`: image A's instance facts
     (PRH_Img.v), the premises of VproC's vrd_cur_entry_call.
   - parse_string by its text, PRH_FnReader.tparse_string_specX (kit blob fb7b12dfa169), as a Section hypothesis.
   parse_string's two live-count premises at the call are vrd_disp_body's conjuncts (VrdPro.v), so the arm lemmas
   state none of them; the instance fact cf_head = PresetReqAt.HEAD is their Section hypothesis HI_head. *)

(* the symbolic pieces of the two straight-line stretches. The node v is atom 19 (s3) and the shadow offset
   atom 23 (s7), as VrdPro.vrd_regs pins them; vrs_SH says the node's 56 bytes are addressable, which is
   exactly prhPv_node's range_addressable, and it is what makes the two ASan gates (rows 135-138 for the
   4-byte store and rows 144-147 for the 8-byte store at v + 16) resolve by the engine's `covered` path, so
   both runs leave sh_obls = [] and no errpath_* call is reachable. *)
#[local] Definition vrs_pc0 : Z := 4 * 4817.
#[local] Definition vrs_pc1 : Z := 4 * 4825.
#[local] Definition vrs_pc2 : Z := 4 * 4907.
#[local] Definition vrs_node (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 19%nat) 0 56 wlo whi [].
#[local] Definition vrs_facts : facts :=
  mkFacts [(19%nat, mkAF 4096 (2 ^ 47 - 57) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
#[local] Definition vrs_ss0 : sstate := mkSS vrs_pc0 sr_atoms [vrs_node 0 4] None vrs_facts.
#[local] Definition vrs_ss1 : sstate := mkSS vrs_pc1 sr_atoms [vrs_node 16 24] None vrs_facts.
#[local] Definition vrs_Bx : sv := SOff 23 0.
#[local] Definition vrs_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
#[local] Definition vrs_SH : list shent := [mkSHE 19 0 56].

(* the bytes a straight-line stretch does not write keep their value (FuzzStrdupB.sd_aview_of_frame's form,
   restated here over this image's SEGS) *)
#[local] Lemma vrs_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* ---- the transport toolkit: what a straight-line stretch that writes only inside [lo, hi) keeps ---- *)

(* the raw byte at an address the stretch does not write *)
#[local] Lemma vrs_raw_of_frame : forall (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs m m' -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros E' rs m m' a HF Hn Ha. apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* a byte that keeps its value keeps its writability *)
#[local] Lemma vrs_wr_eq : forall (Hh : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  writable_at SEGS (mrestrict Hh m) a -> writable_at SEGS (mrestrict Hh m') a.
Proof.
intros Hh m m' a Heq Hw. unfold writable_at, wview, mrestrict in *. rewrite Heq. exact Hw.
Qed.

(* a byte run keeps its value *)
#[local] Lemma vrs_garr8_keep : forall (Wx : world SEGS) (m m' : word -> option byte) a l,
  garr8 SEGS (mrestrict (w_H Wx) m) a l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H Wx) m' (a + Z.of_nat j) = aview SEGS (w_H Wx) m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H Wx) m') a l.
Proof.
intros Wx m m' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (val_mem_kept SEGS (w_H Wx) (w_H Wx) m m' (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. replace (a + Z.of_nat j + kk) with (a + Z.of_nat j) by lia. apply Hk. exact Hj.
Qed.

(* the cursor's three cells and the text survive a stretch that writes neither *)
#[local] Lemma vrs_in_ok_keep : forall (Wx : world SEGS) (m m' : word -> option byte) q text len p0 dd tb,
  pj_in_okR SEGS (mrestrict (w_H Wx) m) q text len p0 dd tb ->
  (forall a, q <= a < q + 24 -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a) ->
  (forall a, q <= a < q + 24 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, text <= a < text + len -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a) ->
  pj_in_okR SEGS (mrestrict (w_H Wx) m') q text len p0 dd tb.
Proof.
intros Wx m m' q text len p0 dd tb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hkq Hrq Hkt.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
- apply (val_mem_kept SEGS (w_H Wx) (w_H Wx) m m' q 8 p0); [intros k Hk; apply Hkq; lia | exact H1].
- apply (val_mem_kept SEGS (w_H Wx) (w_H Wx) m m' (q + 8) 8 (text + len)); [intros k Hk; apply Hkq; lia | exact H2].
- apply (val_mem_kept SEGS (w_H Wx) (w_H Wx) m m' (q + 16) 4 dd); [intros k Hk; apply Hkq; lia | exact H3].
- intros x Hx. apply (vrs_wr_eq (w_H Wx) m m' x); [apply Hrq; lia | apply H4; lia].
- exact H5.
- exact H6.
- exact H7.
- exact H8.
- exact H9.
- apply (vrs_garr8_keep Wx m m' text tb H10). intros j Hj. apply Hkt. lia.
- exact H11.
- exact H12.
Qed.

(* ---- the grammar side: the arm's granted trace IS parse_string's own ---- *)

(* rest_atR at the byte after the opening quote *)
#[local] Lemma vrs_rest_succ : forall tb text p0, text <= p0 ->
  rest_atR tb text (p0 + 1) = skipn 1 (rest_atR tb text p0).
Proof.
intros tb text p0 Hp. unfold rest_atR. rewrite skipn_skipn. f_equal. lia.
Qed.

(* the granted trace of parse_value at a cursor whose first non-white byte is a quote is the granted trace of
   parse_string over the text after that quote: the kit's tparse_string_specX charges
   prhPv_rk (prhPs_gtrace ..) and this slice's text charges prhPv_rk (prhPv_gtrace d ..), and the two are the
   SAME LIST. (This is what closed the room over-charge this lane reported at the pause: the kit now cites the
   model, so no up-grade premise is left.) *)
#[local] Lemma vrs_gtrace_str : forall x y, PjGrammar.skip x = 34 :: y ->
  prhPv_gtrace d x = prhPs_gtrace y.
Proof.
intros x y Hs. unfold prhPv_gtrace, prhPs_gtrace.
rewrite (vrd_str_model prh_jr_strtod d y x [] Hs). unfold PjGrammar.jbind.
destruct (PjGrammar.jr_string y []) as [[r t] ok1]. destruct r as [[s rr]|].
- cbn [PjGrammar.jret fst snd]. rewrite app_nil_r. reflexivity.
- reflexivity.
Qed.

(* the granted trace of a quote that scans: one allocation of Q + 1 bytes, and a free when the escape sequence
   is bad. Both shapes have the same largest request and the same peak. *)
#[local] Lemma vrs_gtrace_scan : forall y Q, PjGrammar.scan y = Some Q ->
  prhPs_gtrace y = [PjGrammar.EAlloc (S Q)] \/
  prhPs_gtrace y = [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)].
Proof.
intros y Q Hs. unfold prhPs_gtrace, PjGrammar.jr_string. rewrite Hs.
unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take, PjGrammar.jfree, PjGrammar.jrefuse.
destruct (PjGrammar.decode y) as [sr|].
- left. cbn [PjGrammar.jret fst snd]. reflexivity.
- right. cbn [fst snd]. reflexivity.
Qed.

(* ---- transport helpers the two straight-line stretches need ---- *)

(* every stack need is a length: PrhImg's pi_frame_nonneg and the shape of zmaxl *)
#[local] Lemma vrs_zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. intros l. unfold zmaxl. induction l as [|x l IH]; cbn [fold_right]; lia. Qed.

#[local] Lemma vrs_STK_ps_nonneg : 0 <= STK_parse_string.
Proof.
unfold STK_parse_string. pose proof (pi_frame_nonneg F_parse_string).
pose proof (vrs_zmaxl_nonneg [STK_fuzz_free; STK_fuzz_malloc; STK_hex4; STK_put_utf8]). lia.
Qed.

(* two blocks of one state that share a byte are the same block *)
#[local] Lemma vrs_blocks_eq : forall ly S Hp (Wx : world SEGS) m md b n b' n' x,
  ARx ly S Hp Wx m md -> In (b, n) (ablocks B ly S) -> In (b', n') (ablocks B ly S) ->
  b <= x < b + req_size n -> b' <= x < b' + req_size n' -> (b, n) = (b', n').
Proof.
intros ly S Hp Wx m md b n b' n' x HAR H1 H2 Hx1 Hx2.
destruct (list_eq_dec Z.eq_dec [b; n] [b'; n']) as [Heq | Hne].
- injection Heq as -> ->. reflexivity.
- exfalso. assert (Hp2 : (b, n) <> (b', n')) by (intros E; injection E as -> ->; exact (Hne eq_refl)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp Wx m md b n b' n' HAR H1 H2 Hp2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a frame's shadow granule for any byte of the frame lies in the frame's shadow range *)
#[local] Lemma vrs_frame_shadow_in : forall F bs x, F mod 8 = 0 -> bs mod 8 = 0 -> 0 <= bs ->
  F <= x < F + bs -> SHADOW_OFF + F / 8 <= SHADOW_OFF + x / 8 < SHADOW_OFF + F / 8 + bs / 8.
Proof.
intros F bs x HF Hbs Hbs0 Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod bs 8 ltac:(lia)) as DB.
assert (F / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (x / 8 < F / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* a frame class big enough to hold a node is a real class (the shift is to the left) *)
#[local] Lemma vrs_cid_nonneg : forall c, 56 <= fs_frame_bytes c -> 0 <= c.
Proof.
intros c H. destruct (Z_le_gt_dec 0 c) as [Hc | Hc]; [exact Hc | exfalso].
unfold fs_frame_bytes in H. replace c with (- (- c)) in H by lia.
rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 in H by lia.
assert (H2 : 2 <= 2 ^ (- c)) by (replace 2 with (2 ^ 1) at 1 by reflexivity; apply Z.pow_le_mono_r; lia).
pose proof (Z.div_le_compat_l 64 2 (2 ^ (- c)) ltac:(lia) ltac:(lia)) as Hd.
change (64 / 2) with 32 in Hd. lia.
Qed.

(* and then it is a whole number of shadow granules *)
#[local] Lemma vrs_fsb_mod8 : forall c, 0 <= c -> fs_frame_bytes c mod 8 = 0.
Proof.
intros c Hc. rewrite (fs_frame_bytes_eq c Hc).
replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z_mod_mult.
Qed.

(* the block an allocator call appends is disjoint from every block that was already there *)
#[local] Lemma vrs_sep_last : forall ly S Hp (Wx : world SEGS) m md bl nb b n,
  ARx ly S Hp Wx m md -> ablocks B ly S = bl ++ [nb] -> In (b, n) bl ->
  zdisjoint (b, req_size n) (fst nb, req_size (snd nb)).
Proof.
intros ly S Hp Wx m md bl nb b n HAR Heq Hin.
destruct (alx_sep SEGS B ARx LAWS ly S Hp Wx m md HAR) as [Hq _].
apply pairwise_app_l in Hq as [Hq _]. rewrite Heq in Hq.
apply in_split in Hin as (l1 & l2 & Hbl). rewrite Hbl in Hq.
rewrite <- app_assoc in Hq. cbn [app] in Hq. rewrite !map_app in Hq.
cbn [map app] in Hq. rewrite !map_app in Hq. cbn [map app fst snd] in Hq.
exact (pairwise_In2 zdisjoint _ (b, req_size n) (fst nb, req_size (snd nb))
         (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1)
         (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2) [] Hq eq_refl).
Qed.

(* the allocator's five statics keep their bytes across a stretch that writes only client memory *)
#[local] Lemma vrs_pst_keep : forall (Wx : world SEGS) (m m' : word -> option byte) lo hi,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a) ->
  (forall a, Exists (in_zr a) prh_pst -> in_img SEGS a) ->
  (forall a, lo <= a < hi -> ~ in_img SEGS a) ->
  forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx m m' lo hi HK HPSTi Hni a Ha. pose proof (HPSTi a Ha) as Hi.
pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hlow.
apply HK; [unfold kLowMemEnd in Hlow; lia | intros Hr; exact (Hni a Hr Hi)].
Qed.

(* the ledger rides on a stretch that keeps the statics and the harness blocks' head words: S1Ledger's
   prh_ledger_kept_aview (which reads prh_pst through its named prh_pst_live .. prh_pst_ran) at the same blocks *)
#[local] Lemma vrs_ledger_keep : forall ly S Hp (Wx : world SEGS) (m m' : word -> option byte)
    Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp Wx m Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a) ->
  (forall a kk i, In (a, kk) Lam -> 0 <= i < 8 ->
     aview SEGS (w_H Wx) m' (a - cf_head + i) = aview SEGS (w_H Wx) m (a - cf_head + i)) ->
  prh_ledger B ly S Hp Wx m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp Wx m m' Lam peak cnt fail ran most own HLed Hs Hh.
exact (S1Ledger.prh_ledger_kept_aview B ly S Hp Wx m ly S Hp Wx m' Lam peak cnt fail ran most own HLed Hs Hh
  (fun a k _ H => H) (Permutation_refl Hp)).
Qed.

(* ---- THE ARM: rows 135..151, joining the epilogue at ROW 225 - vrd_str_a_ok, Qed in lib/A/VrdArmStrOk.v (kept in
   its own file so this one, which four lanes import, stays fast) ---- *)

End arms.
