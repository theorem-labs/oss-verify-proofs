(* fuzz_preset, slice S5b, lane VnumD (worker a Theorem Labs lane): parse_value's NUMBER ARM in image A from the dispatch to the
   token scan's exit - listing rows 157..267 of the neutral per-function listing of the pinned rebuilt image A
   (parse_value's disassembly in the #102 pin A' image; row 1 is the entry 0x85f10).
   rule 24: no function is proved here (kind: segment lemma). The entry state is VproC's dispatch body
   (VrdPro.vrd_disp_body at arm VA_num); the conclusion is VnumE's boundary VrdNumTail.vrd_num266_a at row 267, or,
   for the three refusals before any allocation (rows 162, 170, 182), the state vrd_num326_a at row 326 defined below
   in the same shape. The segments composed are lib/A/VrdNum.v's vrd_seg_sa (rows 157..162), vrd_seg_163
   (rows 163..192) and vrd_loop (rows 193..208, 266); this file runs no instruction of its own, it only moves the
   dispatch's facts to each segment's entry and the segments' exits into the two boundaries.

   THE GENERIC MEMORY INVARIANT (a Theorem Labs lane's 12:19Z ruling; lane A2NumP). REASON: an SRr post is opaque once Qed, so
   an end-state memory invariant must be in the segment's STATEMENT; the generic SRr_memnorm was measured NOT provable
   (a Theorem Labs lane), so it cannot be added afterwards. vrd_num_scan / vrd_num_scan_disp / vrd_num_early_epi /
   vrd_num_a_from_tail have _P twins (P with YC80x.srr_inv_laws; the early refusals join through a Theorem Labs lane's
   VrdRefJoinP.vrd_ref_join_P, the one copy of the refusal join with P), and each old statement survives
   BYTE-IDENTICAL as its corollary at P := fun _ => True. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YC80xf
YGcallx YCbqGcall YGcallSx YGcallMx FCiface YStrtodRowX YFclsStep YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog VrdPro VrdNum VrdNumTail VrdRefJoinP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the token, from the scan (pure) ---- *)
Lemma vrd_skipn_rest : forall (tb : list Z) text p' (j : nat), text <= p' ->
  skipn j (rest_atR tb text p') = rest_atR tb text (p' + Z.of_nat j).
Proof.
intros tb text p' j Hp. unfold rest_atR. rewrite skipn_skipn. f_equal. lia.
Qed.

(* row 162 taken: nothing after the sign *)
Lemma vrd_tok_none_short : forall (tb : list Z) text p' b y,
  text <= p' -> rest_atR tb text p' = b :: y ->
  text + Z.of_nat (length tb) <= p' + Z.of_nat (vrd_j b) -> vrd_num_tok (rest_atR tb text p') = None.
Proof.
intros tb text p' b y Hp HR Hle.
assert (Hs : skipn (vrd_j b) (b :: y) = []).
{ rewrite <- HR, (vrd_skipn_rest tb text p' (vrd_j b) Hp). unfold rest_atR. apply skipn_all2. lia. }
rewrite HR. unfold vrd_num_tok. cbv beta zeta iota. rewrite Hs. reflexivity.
Qed.

(* rows 170 / 182 taken: the bytes at s6 fail the model's two tests *)
Lemma vrd_tok_none_lead : forall (tb : list Z) text p' b y,
  text <= p' -> rest_atR tb text p' = b :: y ->
  vrd_lead_ok (rest_atR tb text (p' + Z.of_nat (vrd_j b))) = false -> vrd_num_tok (rest_atR tb text p') = None.
Proof.
intros tb text p' b y Hp HR Hl.
rewrite <- (vrd_skipn_rest tb text p' (vrd_j b) Hp), HR in Hl.
rewrite HR. unfold vrd_num_tok. cbv beta zeta iota. revert Hl.
destruct (skipn (vrd_j b) (b :: y)) as [|c z]; [reflexivity|].
cbn [vrd_lead_ok]. destruct (digit c); cbn [negb andb]; [|reflexivity].
destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end)%bool; cbn [negb]; intros Hl;
  [reflexivity | discriminate Hl].
Qed.

(* the scan's exit s6': the token is the sign and the numch run measured from s6 = p' + j *)
Lemma vrd_tok_some : forall (tb : list Z) text p' b y s6',
  text <= p' -> rest_atR tb text p' = b :: y ->
  vrd_lead_ok (rest_atR tb text (p' + Z.of_nat (vrd_j b))) = true ->
  p' + Z.of_nat (vrd_j b) <= s6' -> s6' <= text + Z.of_nat (length tb) ->
  span numch (rest_atR tb text (p' + Z.of_nat (vrd_j b))) =
    (firstn (Z.to_nat (s6' - (p' + Z.of_nat (vrd_j b)))) (rest_atR tb text (p' + Z.of_nat (vrd_j b))),
     rest_atR tb text s6') ->
  exists txt, vrd_num_tok (rest_atR tb text p') = Some (txt, rest_atR tb text s6') /\
              p' + Z.of_nat (length txt) = s6'.
Proof.
intros tb text p' b y s6' Hp HR Hl Hle Hend Hsp.
assert (Hx : skipn (vrd_j b) (b :: y) = rest_atR tb text (p' + Z.of_nat (vrd_j b)))
  by (rewrite <- HR; apply vrd_skipn_rest; lia).
assert (HL6 : length (rest_atR tb text (p' + Z.of_nat (vrd_j b))) =
              (length tb - Z.to_nat (p' + Z.of_nat (vrd_j b) - text))%nat)
  by (unfold rest_atR; apply length_skipn).
assert (Hj1 : (vrd_j b <= 1)%nat) by (unfold vrd_j; destruct (b =? 45); lia).
destruct (rest_atR tb text (p' + Z.of_nat (vrd_j b))) as [|c z] eqn:E6; [discriminate Hl|].
cbn [vrd_lead_ok] in Hl. apply andb_prop in Hl as [Hd Hz]. apply negb_true_iff in Hz.
cbn [span] in Hsp.
assert (Hn : numch c = true) by (unfold numch; rewrite Hd; reflexivity).
rewrite Hn in Hsp. destruct (span numch z) as [a r] eqn:Ez. injection Hsp as HA Hr.
exists (firstn (vrd_j b) (b :: y) ++ c :: a). split.
- rewrite HR. unfold vrd_num_tok. cbv beta zeta iota. rewrite Hx. cbv beta iota.
  rewrite Hd, Hz. cbn [negb]. rewrite Ez. rewrite Hr. reflexivity.
- rewrite length_app, length_firstn. cbn [length] in HL6 |- *.
  assert (HA' : length (c :: a) = length (firstn (Z.to_nat (s6' - (p' + Z.of_nat (vrd_j b)))) (c :: z)))
    by (rewrite HA; reflexivity).
  rewrite length_firstn in HA'. cbn [length] in HA'. lia.
Qed.

(* the shadow of an application byte is below the stack (the bound the slot exclusions need) *)
Lemma vrd_shadow_rng : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44.
Proof.
intros x Hx. unfold shadow_of_addr.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

(* ---- THE EARLY REFUSALS AT ROW 326 (A 0x86420): rows 162 / 170 / 182 taken, before any allocation. The same shape
   as VrdNumTail.vrd_num266_a, with the token absent (vrd_num_tok = None, the model's three refusals before its
   jalloc) in place of the token and its rest, and no spill (rows 162..182 reach row 326 before row 192). The step from
   here to VrdNum.vrd_ref_a with the arm's result is the refusal model (vnum-NEXT step 7). ---- *)
Definition vrd_num326_a
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)) (CTX0 : list (list Z)) (CW : list (list Z))
  (e q v text len p : Z) (d : nat) (tb : list Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : world segs -> config -> Prop :=
  fun W c =>
  exists (pos p' k1 k : Z) (ly : alayout) (S : astate) (Hp : list Z)
         (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  c = cfg_at segs (BASE + vrd_row 326) regs mem md /\
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch /\
  getr regs0 10 = w64 q /\ getr regs0 11 = w64 v /\
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v /\
  vrd_disp_body B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    VA_num pos p' k1 ly S Hp W regs1 mem1 md1 /\
  vrd_num_tok (rest_atR tb text p') = None /\
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k /\
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
     ~ (spZ regs1 <= a < spZ regs1 + 32) ->
     aview segs (w_H W) mem a = aview segs (w_H W) mem1 a) /\
  mem_grows (rdW W mem1) (rdW W mem) /\
  vrd_kept_regs regs regs1 /\ getr regs 21 = w64 (-1).

(* ---- moving the dispatch's facts ---- *)
Lemma vrd_stk_big2 : forall d, 16384 <= STK_parse_value d.
Proof.
intros d. unfold STK_parse_value, LEAF_pv_pi, zmaxl. cbn [fold_right].
unfold STK_RT_STRTOD, ESTACK.
assert (H0 : 0 <= pi_frame F_parse_value + pi_frame F_parse_items).
{ pose proof (pi_frame_nonneg F_parse_value). pose proof (pi_frame_nonneg F_parse_items). lia. }
pose proof (Z.mul_nonneg_nonneg _ _ (Nat2Z.is_nonneg (S (PjGrammar.MAXD - d))) H0) as H3.
lia.
Qed.

Lemma vrd_garr8_kept_on : forall (W : world segs) (m m' : word -> option byte) text (tb : list Z),
  (forall a, text <= a < text + Z.of_nat (length tb) -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  garr8 segs (rdW W m) text tb -> garr8 segs (rdW W m') text tb.
Proof.
intros W m m' text tb HK HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
eapply val_mem_kept; [|exact V]. intros kk Hk. apply HK. cbn in Hk. lia.
Qed.

Lemma vrd_ra_kept_on : forall (rd rd' : Z -> option Z) (Bz a n : Z),
  (forall x, a <= x < a + n -> rd' (shadow_of_addr Bz x) = rd (shadow_of_addr Bz x)) ->
  range_addressable rd Bz a n -> range_addressable rd' Bz a n.
Proof.
intros rd rd' Bz a n HK H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite HK by exact Hx. auto.
Qed.

(* a byte the dispatch reads as addressable is not shadowed by the call's own frame: the frame's eight shadow
   bytes are all poisoned at the dispatch (VrdPro.vrd_frame_shadow, every entry >= 8) *)
Lemma vrd_ra_off_frame : forall (rd : Z -> option Z) a n F,
  range_addressable rd SHADOW_OFF a n ->
  (forall i, 0 <= i < 8 -> rd (SHADOW_OFF + F / 8 + i) = Some (nth (Z.to_nat i) vrd_frame_shadow 0)) ->
  forall x, a <= x < a + n -> ~ (SHADOW_OFF + F / 8 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + F / 8 + 8).
Proof.
intros rd a n F HRA HF x Hx Hin.
destruct (HRA x Hx) as (s & Hs & Hok).
specialize (HF (shadow_of_addr SHADOW_OFF x - (SHADOW_OFF + F / 8)) ltac:(lia)).
replace (SHADOW_OFF + F / 8 + (shadow_of_addr SHADOW_OFF x - (SHADOW_OFF + F / 8)))
  with (shadow_of_addr SHADOW_OFF x) in HF by lia.
rewrite Hs in HF.
assert (Hi : (Z.to_nat (shadow_of_addr SHADOW_OFF x - (SHADOW_OFF + F / 8)) < 8)%nat) by lia.
assert (Hge : 8 <= s).
{ assert (Hs' : s = nth (Z.to_nat (shadow_of_addr SHADOW_OFF x - (SHADOW_OFF + F / 8))) vrd_frame_shadow 0)
    by congruence.
  rewrite Hs'. clear -Hi.
  destruct (Z.to_nat (shadow_of_addr SHADOW_OFF x - (SHADOW_OFF + F / 8))) as [|[|[|[|[|[|[|[|i]]]]]]]];
    cbn; lia. }
unfold saddr_ok in Hok. destruct Hok as [Hk | [_ Hk]]; lia.
Qed.

(* ---- THE SCAN, rows 157..267: from the dispatch with the number arm selected to vrd_num266_a, or to the early
   refusals vrd_num326_a ---- *)
(* the generic-invariant twin (P with srr_inv_laws through VrdNum's vrd_seg_sa_P / vrd_seg_163_P / vrd_loop_P): P of
   the dispatch memory, and P of the memory at either exit *)
Lemma vrd_num_scan_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own pos p' k1 ly S Hp (W : world segs) regs1 mem1 md1,
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  getr regs0 10 = w64 q -> getr regs0 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v ->
  vrd_disp_body B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    VA_num pos p' k1 ly S Hp W regs1 mem1 md1 ->
  P mem1 ->
  SRr segs W (cfg_at segs (pa_sigma AS_parse_value + vrd_arm_off VA_num) regs1 mem1 md1)
    (fun W' c' =>
       (vrd_num266_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
          most own W' c' \/
        vrd_num326_a ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
          most own W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own pos p' k1 ly S Hp W regs1 mem1 md1 HPRE R10q R11v HRD HB HPM.
pose proof HB as (HRest & Hpp & HM & HJ & HFr & HAB & HHp & _ & HWIN & HFW & HFRAME & HSAV & HREGS & _ & _ & _ & _ &
  HIN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
pose proof (vrd_stk_big2 d) as HSTK.
destruct HFW as (He0 & _ & _ & _).
destruct HIN as (_ & _ & _ & _ & _ & _ & Htl & Hp'r & Hlen & GT & _ & _).
destruct HSRC as (_ & Ht4096 & Hceil & Ham & HRA & _).
rewrite Hlen in Hceil, Ham, HRA.
destruct HREGS as (R2 & R9 & R8 & R18 & R26 & R19 & R20 & R21 & R22 & R25 & R23 & R24 & R27 & R3 & R4 & R10 & R12).
destruct (PjGrammar.skip (rest_atR tb text p)) as [|b y] eqn:Esk; [destruct HM as [Hc _]; discriminate Hc|].
destruct HM as (_ & Hp'e & Hnth & _ & R11).
assert (HinF : In (0, pos) (frames S)) by (rewrite HFr; left; reflexivity).
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTACK & _).
destruct HSTACK as (_ & _ & Hclo & Hlo & Hhi & H47 & _).
destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem1 md1 0 pos HAR HinF) as (HF0 & HFc & HFapp).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc.
assert (HD8 : 0 <= frame_addr ly 0 pos / 8 <= alloc_ceiling / 8).
{ split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
assert (HAC8 : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
(* the stack frame base sp = s1 *)
assert (Hsp0 : 0 <= spZ regs0 - 160 - (spZ regs0 - 160) mod 32 < 2 ^ 64).
{ pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(lia)). lia. }
assert (HSP : spZ regs1 = spZ regs0 - 160 - (spZ regs0 - 160) mod 32)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; exact Hsp0).
assert (Hspm : spZ regs1 mod 32 = 0).
{ rewrite HSP. pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(lia)).
  rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
assert (Hspb : spZ regs0 - 192 < spZ regs1 <= spZ regs0 - 160).
{ rewrite HSP. pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(lia)). lia. }
(* the dispatch byte b and the rest from p' *)
assert (Hb : nth (Z.to_nat (p' - text)) tb 0 = b) by (apply nth_error_nth; exact Hnth).
destruct (vrd_garr8_byte (rdW W mem1) text tb p' GT ltac:(lia)) as [_ Rb]. rewrite Hb in Rb.
assert (HR : rest_atR tb text p' = b :: y)
  by (first [exact HRest | rewrite HRest; exact Esk]).
assert (HDX : forall x, text <= x < text + len -> ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <=
           shadow_of_addr SHADOW_OFF x < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8))
  by (apply (vrd_ra_off_frame _ text len _ HRA); exact (proj2 (proj2 (proj2 HFRAME)))).
replace (pa_sigma AS_parse_value + vrd_arm_off VA_num) with (BASE + vrd_row 157) by (vm_compute; reflexivity).
eapply (vrd_seg_sa_P B ARx SK LAWS P PLAW d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k1 W regs1 mem1 md1 b p'
  text len _ HJ HPM HinF R24 R10 R11 R12 Rb Ht4096 Hp'r Htl).
- (* row 162 taken *)
  intros regs' mem' md' k' HJ' HPM' HK' HG' HKR' R21' R22' R13' Hshort.
  apply SRr_ret. split; [|exact HPM']. right.
  exists pos, p', k1, k', ly, S, Hp, regs1, mem1, md1, regs', mem', md'.
  split; [reflexivity|]. split; [exact HPRE|]. split; [exact R10q|]. split; [exact R11v|]. split; [exact HRD|].
  split; [exact HB|].
  split; [apply (vrd_tok_none_short tb text p' b y ltac:(lia) HR); lia|].
  split; [exact HJ'|].
  split; [intros a Ha64 Hsh _; exact (HK' a Ha64 Hsh)|].
  split; [exact HG'|]. split; [exact HKR'|]. exact R21'.
- (* row 163 *)
  intros regs' mem' md' k' HJ' HPM' HK' HG' HKR' R21' R22' R13' Hlt.
  pose proof HKR' as (K2 & K3 & K4 & K8 & K9 & K10 & K12 & K18 & K19 & K20 & K23 & K24 & K26 & K27).
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTP' & _).
  set (s6 := p' + Z.of_nat (vrd_j b)) in *.
  assert (Hj1 : 0 <= Z.of_nat (vrd_j b) <= 1) by (unfold vrd_j; destruct (b =? 45); cbn; lia).
  (* the text, the shadow of the text, the stack slot, at mem' *)
  assert (KT' : forall a, text <= a < text + len -> aview segs (w_H W) mem' a = aview segs (w_H W) mem1 a).
  { intros a Ha. apply HK'; [lia|]. unfold amem_range in Ham. lia. }
  assert (GT' : garr8 segs (rdW W mem') text tb)
    by (apply (vrd_garr8_kept_on W mem1); [rewrite Hlen; exact KT' | exact GT]).
  assert (HRA' : range_addressable (aview segs (w_H W) mem') SHADOW_OFF text len).
  { apply (vrd_ra_kept_on (aview segs (w_H W) mem1)); [|exact HRA].
    intros x Hx. assert (Hx47 : 0 <= x < 2 ^ 47) by (unfold amem_range in Ham; lia).
    pose proof (vrd_shadow_rng x Hx47) as Hsx.
    apply HK'; [lia|].
    exact (HDX x Hx). }
  assert (Wst : forall o, 16 <= o < 24 -> writable_at segs (rdW W mem') (spZ regs1 + o)).
  { intros o Ho. apply (apresent_writable segs). apply HSTP'. lia. }
  assert (H9' : bv_unsigned (getr regs' 9) = spZ regs1) by (rewrite K9, R9; reflexivity).
  eapply (vrd_seg_163_P B ARx SK LAWS P PLAW d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k' W regs' mem' md'
    p' (Z.of_nat (vrd_j b)) s6 (spZ regs1) (frame_addr ly 0 pos) text len tb _ HJ' HPM' R22'
    ltac:(rewrite K10; exact R10) R13' eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite K23; exact R23)
    ltac:(rewrite K26; exact R26) ltac:(lia) ltac:(lia) H9' ltac:(lia) Hspm ltac:(lia) ltac:(lia)
    ltac:(rewrite K12; exact R12) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ham GT' Hlen HRA' Wst).
  + (* rows 170 / 182 taken *)
    intros regs'' mem'' md'' k'' HJ'' HPM'' HK'' HG'' HKR'' R21'' Hlead.
    apply SRr_ret. split; [|exact HPM'']. right.
    exists pos, p', k1, k'', ly, S, Hp, regs1, mem1, md1, regs'', mem'', md''.
    split; [reflexivity|]. split; [exact HPRE|]. split; [exact R10q|]. split; [exact R11v|]. split; [exact HRD|].
    split; [exact HB|].
    split; [exact (vrd_tok_none_lead tb text p' b y ltac:(lia) HR Hlead)|].
    split; [exact HJ''|].
    split; [intros a Ha64 Hsh Hst; rewrite (HK'' a Ha64 ltac:(lia)); exact (HK' a Ha64 Hsh)|].
    split; [exact (vrd_mg_trans _ _ _ HG' HG'')|].
    split; [exact (vrd_kept_trans _ _ _ HKR'' HKR')|].
    rewrite R21''. exact R21'.
  + (* row 193: the scan *)
    intros regs'' mem'' md'' k'' HJ'' HPM'' HK'' HG'' VSP HKR'' R21'' R22'' R11'' R13'' R14'' R15'' Hlead.
    pose proof HKR'' as (L2 & L3 & L4 & L8 & L9 & L10 & L12 & L18 & L19 & L20 & L23 & L24 & L26 & L27).
    assert (KT'' : forall a, text <= a < text + len -> aview segs (w_H W) mem'' a = aview segs (w_H W) mem' a)
      by (intros a Ha; apply HK''; lia).
    assert (GT'' : garr8 segs (rdW W mem'') text tb)
      by (apply (vrd_garr8_kept_on W mem'); [rewrite Hlen; exact KT'' | exact GT']).
    assert (HRA'' : range_addressable (aview segs (w_H W) mem'') SHADOW_OFF text len).
    { apply (vrd_ra_kept_on (aview segs (w_H W) mem')); [|exact HRA'].
      intros x Hx. assert (Hx47 : 0 <= x < 2 ^ 47) by (unfold amem_range in Ham; lia).
      pose proof (vrd_shadow_rng x Hx47) as Hsx.
      apply HK''; lia. }
    eapply (vrd_loop_P B ARx SK LAWS P PLAW (Z.to_nat (text + len - s6)) d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly
      S Hp W regs'' mem'' md'' k'' s6 text len tb _ ltac:(lia) HJ'' HPM'' ltac:(rewrite R22''; exact R22') R11''
      ltac:(rewrite L12, K12; exact R12) R13'' R14'' R15'' ltac:(rewrite L23, K23; exact R23)
      ltac:(lia) Hlt ltac:(lia) Ham GT'' Hlen HRA'').
    intros regs3 mem3 md3 k3 s6' HJ3 HPM3 HK3 HG3 HKR3 R21c R22c Hs6' Hsp.
    destruct (vrd_tok_some tb text p' b y s6' ltac:(lia) HR Hlead ltac:(lia) ltac:(lia) Hsp) as (txt & Htok & Hlt').
    apply SRr_ret. split; [|exact HPM3]. left.
    exists pos, p', k1, k3, ly, S, Hp, regs1, mem1, md1, regs3, mem3, md3, txt, (rest_atR tb text s6').
    split; [reflexivity|]. split; [exact HPRE|]. split; [exact R10q|]. split; [exact R11v|]. split; [exact HRD|].
    split; [exact HB|].
    split; [exact Htok|].
    split; [rewrite Hlt'; reflexivity|].
    split; [exact HJ3|].
    split.
    { intros a Ha64 Hsh Hst. rewrite (HK3 a), (HK'' a Ha64 ltac:(lia)). exact (HK' a Ha64 Hsh). }
    split; [intros a Ha; exact (apresent_grows (w_H W) mem1 mem3 a (vrd_mg_trans _ _ _ (vrd_mg_trans _ _ _ HG' HG'') HG3) Ha)|].
    split; [exact (vrd_kept_trans _ _ _ HKR3 (vrd_kept_trans _ _ _ HKR'' HKR'))|].
    split; [rewrite R21c, R21''; exact R21'|].
    split; [rewrite Hlt'; exact R22c|].
    eapply val_mem_kept; [|exact VSP]. intros kk _. apply HK3.
Qed.

(* the old statement, byte-identical: vrd_num_scan_P at P := fun _ => True *)
Lemma vrd_num_scan : forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own pos p' k1 ly S Hp (W : world segs) regs1 mem1 md1,
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  getr regs0 10 = w64 q -> getr regs0 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v ->
  vrd_disp_body B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    VA_num pos p' k1 ly S Hp W regs1 mem1 md1 ->
  SRr segs W (cfg_at segs (pa_sigma AS_parse_value + vrd_arm_off VA_num) regs1 mem1 md1)
    (fun W' c' =>
       vrd_num266_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
         most own W' c' \/
       vrd_num326_a ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
         most own W' c').
Proof.
intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own pos p' k1 ly S Hp W regs1 mem1 md1 HPRE R10q R11v HRD HB.
eapply SRr_mono.
- exact (vrd_num_scan_P (fun _ => True) (srr_inv_laws_true segs) ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text
    len p d tb Lam peak cnt fail ran most own pos p' k1 ly S Hp W regs1 mem1 md1 HPRE R10q R11v HRD HB I).
- intros W' c' _ (H & _). exact H.
Qed.

(* ---- the same from the dispatch boundary itself (VrdPro.vrd_disp_a), the number arm selected ---- *)
(* the generic-invariant twin *)
Lemma vrd_num_scan_disp_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own (W : world segs) (c : config),
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  getr regs0 10 = w64 q -> getr regs0 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  match PjGrammar.skip (rest_atR tb text p) with b :: _ => vrd_arm_of b = VA_num | [] => False end ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c
    (fun W' c' =>
       (vrd_num266_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
          most own W' c' \/
        vrd_num326_a ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
          most own W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c
  HPRE R10q R11v HRD (arm & pos & p' & k1 & ly & S & Hp & regs1 & mem1 & md1 & -> & HB) Harm HPM.
assert (Ha : arm = VA_num).
{ pose proof HB as (_ & _ & HM & _).
  destruct (PjGrammar.skip (rest_atR tb text p)) as [|b y]; [contradiction|].
  destruct HM as (-> & _). exact Harm. }
subst arm.
exact (vrd_num_scan_P P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own pos p' k1 ly S Hp W regs1 mem1 md1 HPRE R10q R11v HRD HB HPM).
Qed.

(* the old statement, byte-identical: vrd_num_scan_disp_P at P := fun _ => True *)
Lemma vrd_num_scan_disp : forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own (W : world segs) (c : config),
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  getr regs0 10 = w64 q -> getr regs0 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  match PjGrammar.skip (rest_atR tb text p) with b :: _ => vrd_arm_of b = VA_num | [] => False end ->
  SRr segs W c
    (fun W' c' =>
       vrd_num266_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
         most own W' c' \/
       vrd_num326_a ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
         most own W' c').
Proof.
intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c HPRE R10q R11v HRD HDISP HARM.
eapply SRr_mono.
- exact (vrd_num_scan_disp_P (fun _ => True) (srr_inv_laws_true segs) ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v
    text len p d tb Lam peak cnt fail ran most own W c HPRE R10q R11v HRD HDISP HARM I).
- intros W' c' _ (H & _). exact H.
Qed.

(* ---- STEP 7a: the early refusals (rows 162 / 170 / 182, vrd_num326_a) as the number arm's refusal join
   VrdNum.vrd_ref_a, with the arm's result vrd_pv_post at res = None, ok = [], tr = [], D = []: the model refuses
   (vrd_num_tok = None), nothing is allocated, the ledger and the cursor / node bytes are the dispatch's (rows
   157..182 write only the frame's shadow granule 4 and the stack slot [sp + 16, sp + 24)). The live set, the position
   transfer and the outcome are the entry's across the fake-frame take (S = set_fs f S0: room_of_cf and
   iface_room_pos read no frame, PresetRoomPosKeep.room_pos_set_fs), at E = rd_hevs [] = [] and the granted trace
   prhPv_gtrace = [] (the refusal precedes the model's allocation).
   H_pst_img is an IMAGE fact (the five alloc.c statics are image bytes): the instance supplies it
   (lib/A/Prog/S1ImgA.v pst_in_img_A at prh_img_A). ---- *)
Lemma vrd_num_ref_early : forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own (W : world segs) (c : config),
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  vrd_num326_a ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own W c ->
  exists pos, vrd_ref_a B ARx SK d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos (-1)
    (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos (-1))
    W c.
Proof.
intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c H_pst_img
  (pos & p' & k1 & k & ly & S & Hp & regs1 & mem1 & md1 & regs & mem & md & -> & HPRE & R10q & R11v & HRD & HB &
   Htok & HJ & HK & HG & HKR & R21).
exists pos.
pose proof HB as (HRest & Hpp & HM & HJ1 & HFr & HAB & HHp & HFS & HWIN & HFW & HFRAME & HSAV & HREGS & _ & _ & _ & _ &
  HIN & _ & HNODE & _ & Hq0 & Hq1 & _ & _ & _ & Hra & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED & HROOM &
  _ & _ & _ & _ & _ & _ & HFZ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
pose proof (vrd_stk_big2 d) as HSTK.
pose proof cf_head_nonneg as Hch.
destruct HFW as (He0 & _ & _ & _).
destruct HREGS as (R2 & R9 & R8 & R18 & R26 & R19 & R20 & R21d & R22 & R25 & R23 & R24 & R27 & R3 & R4 & R10 & R12).
pose proof HKR as (K2 & K3 & K4 & K8 & K9 & K10 & K12 & K18 & K19 & K20 & K23 & K24 & K26 & K27).
assert (HinF : In (0, pos) (frames S)) by (rewrite HFr; left; reflexivity).
pose proof (proj1 HJ1) as HAR. cbv beta in HAR.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTACK & _).
destruct HSTACK as (_ & _ & Hclo & Hlo & Hhi & H47 & _).
destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem1 md1 0 pos HAR HinF) as (HF0 & HFc & HFapp).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc, HFapp.
assert (HD8 : 512 <= frame_addr ly 0 pos / 8 <= alloc_ceiling / 8).
{ split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_mono; lia]. }
assert (HAC8 : alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
assert (Hsp0 : 0 <= spZ regs0 - 160 - (spZ regs0 - 160) mod 32 < 2 ^ 64).
{ pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(lia)). lia. }
assert (HSP : spZ regs1 = spZ regs0 - 160 - (spZ regs0 - 160) mod 32)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; exact Hsp0).
assert (Hspb : spZ regs0 - 192 < spZ regs1 <= spZ regs0 - 160).
{ rewrite HSP. pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(lia)). lia. }
(* the bytes rows 157..182 leave alone: everything at or above the stack slot, and the application below it *)
assert (KHI : forall a, spZ regs1 + 32 <= a < 2 ^ 64 -> aview segs (w_H W) mem a = aview segs (w_H W) mem1 a)
  by (intros a Ha; apply HK; lia).
assert (KLO : forall a, 0 <= a -> a < alloc_ceiling + 64 -> ~ (kLowShadowBeg + 512 <= a < kHighMemBeg) ->
          aview segs (w_H W) mem a = aview segs (w_H W) mem1 a)
  by (intros a H1 H2 H3; apply HK; lia).
exists regs, mem, md, ly, S, Hp, k.
split; [first [rewrite <- vrd_pc_ref; reflexivity | unfold cfg_at; rewrite <- vrd_pc_ref; reflexivity
              | unfold cfg_at; f_equal; f_equal; vm_compute; reflexivity]|].
split; [exact HJ|].
split; [intros a Ha Hn; rewrite KHI by lia; exact (HWIN a Ha Hn)|].
split; [rewrite K8; exact R8|]. split; [rewrite K18; exact R18|]. split; [rewrite K26; exact R26|].
split; [rewrite K24; exact R24|]. split; [exact R21|].
split; [rewrite K3; exact R3|]. split; [rewrite K4; exact R4|]. split; [exact Hra|].
split.
{ unfold vrd_saved in HSAV |- *.
  destruct HSAV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  repeat split; (eapply val_mem_kept; [|eassumption]); intros kk Hk; cbn in Hk; apply KHI; lia. }
split.
{ destruct HFRAME as (_ & _ & HFL & _).
  eapply val_mem_kept; [|exact HFL]. intros kk Hk. cbn in Hk.
  unfold in_app, ASAN_CEIL in HFapp. apply KLO; lia. }
split; [exact HinF|]. split; [exact HFZ|]. split; [exact He0|].
(* the arm's result *)
destruct HFS as (f & HSf). subst S.
(* read by conjunct SHAPE, not position (decompose [and]): Batch 2's E sweep appends g_most's cell to prh_glob *)
assert (HGL : 0 <= Ledger.lsum Lam <= peak /\ 0 <= cnt < 2 ^ 64)
  by (destruct HLED as (HG0 & _); clear - HG0; unfold prh_glob in HG0; decompose [and] HG0; lia).
(* the model refuses before its allocation, at ANY strtod oracle: so the instance reading (ReaderRes.jr_strtod) and
   the granted trace (prhPv_gtrace, over prh_jr_strtod) both make no event *)
assert (HJVs : forall sm, jr_value sm d (rest_atR tb text p) [] = (None, [], [])).
{ intros sm.
  destruct (PjGrammar.skip (rest_atR tb text p)) as [|b y] eqn:Esk; [destruct HM as [Hc _]; discriminate Hc|].
  destruct HM as (Harm & _).
  assert (HR : rest_atR tb text p' = b :: y) by (first [exact HRest | rewrite HRest; exact Esk]).
  assert (N6 : b <> 123 /\ b <> 91 /\ b <> 34 /\ b <> 116 /\ b <> 102 /\ b <> 110).
  { unfold vrd_arm_of in Harm. repeat split; intros Hb; subst b; cbn in Harm; discriminate Harm. }
  destruct N6 as (N1 & N2 & N3 & N4 & N5 & N6).
  rewrite (vrd_jr_value_number sm d (rest_atR tb text p) b y [] Esk N1 N2 N3 N4 N5 N6).
  rewrite vrd_num_tok_spec, <- HR, Htok. reflexivity. }
pose proof (HJVs ReaderRes.jr_strtod) as HJV.
assert (HGT : prhPv_gtrace d (rest_atR tb text p) = []) by (unfold prhPv_gtrace; rewrite (HJVs prh_jr_strtod); reflexivity).
(* the model's free-order list at a number: the leaf's list of the value's own trace (VrdNum.vrd_frees_leaf) *)
assert (HFL : prhPv_frees d (rest_atR tb text p) [] =
  PresetReqAt.lf (snd (fst (jr_value ReaderRes.jr_strtod d (rest_atR tb text p) [])))).
{ destruct (PjGrammar.skip (rest_atR tb text p)) as [|b y] eqn:Esk; [destruct HM as [Hc _]; discriminate Hc|].
  destruct HM as (Harm & _). unfold vrd_arm_of in Harm.
  apply (vrd_frees_leaf d _ [] b y Esk); intros Hb; subst b; cbn in Harm; discriminate Harm. }
unfold vrd_pv_post.
exists [], None, [], [], [], Lam, peak, cnt, fail, ran.
split; [exact HJV|].
split.
{ apply (S1Ledger.prh_ledger_kept_aview B ly (set_fs f S0) Hp W mem1 ly (set_fs f S0) Hp W mem Lam peak cnt fail ran
    most own HLED).
  - intros a Ha. pose proof (@pa_segs_low _ A_prog_listing PI_prog_A a (H_pst_img a Ha)) as Hlo'. apply HK; lia.
  - intros a k0 i Hin Hi.
    destruct HLED as (_ & _ & HFA & _). rewrite Forall_forall in HFA.
    destruct (HFA (a, k0) Hin) as (Hk0 & Hab & _ & _ & _). cbn [fst snd] in Hk0, Hab.
    destruct (alx_blocks segs B ARx LAWS ly (set_fs f S0) Hp W mem1 md1 _ _ HAR Hab) as (_ & Hb4 & Hbc & Hbapp & _).
    assert (Hn0 : 0 <= k0 + cf_head) by lia.
    pose proof (req_size_pos (k0 + cf_head) Hn0) as Hrq.
    unfold in_app, ASAN_CEIL in Hbapp. apply KLO; lia.
  - intros a k0 _ H. exact H.
  - apply Permutation_refl. }
split; [exact (proj1 HROOM)|].
(* the hull use: the fake-frame take keeps st_secs, so both meters are the entry's *)
split; [exact (PresetHullBudget.hull_used_secs S0 (set_fs f S0) _ eq_refl)|].
(* the live set: set_fs moves no block, and E = [] *)
split; [exact (Permutation_refl _)|].
(* THE POSITION TRANSFER at E = []: the frame take keeps the position (by conversion) *)
split.
{ intros sm x os i H0 hist HP _. exists hist. cbn [PresetReqAt.rd_hevs flat_map length]. rewrite Nat.add_0_r.
  exact (PresetRoomPosKeep.room_pos_set_fs sm x os i H0 hist S0 f HP). }
(* THE OUTCOME: the granted trace is empty, the instance's reading is the granted one at every ok *)
split.
{ intros sm x os i H0 hist HP _ _ _. split; [reflexivity|]. split; [rewrite HJV; reflexivity|].
  exists hist. rewrite HGT. cbn [PresetReqAt.rd_hevs flat_map length]. rewrite Nat.add_0_r.
  exact (PresetRoomPosKeep.room_pos_set_fs sm x os i H0 hist S0 f HP). }
(* THE OUTCOME OF AN INJECTED READING: the instance made no call (tr = []), so no outcome failed *)
split; [intros sm x os i H0 hist _ _ _ _ ii Hii; cbn in Hii; lia|].
split.
{ rewrite HGT. unfold rd_ledger_move. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold prh_oks. cbn. split; [intros i Hi; lia|]. split; [left; reflexivity | intros i Hi; lia].
  - cbn. rewrite Z.add_0_r, Z.mod_small by lia. reflexivity.
  - unfold fail_afterR. cbn. split; intros H; [lia | reflexivity].
  - cbn [app]. apply Permutation_refl.
  - cbn. apply Permutation_refl.
  - reflexivity.
  - unfold prh_refused_peak. cbn. lia. }
split; [intros a k0 Hin; destruct Hin|].
split; [cbn [prhReader_ab map app]; rewrite HAB; apply Permutation_refl|].
split; [rewrite HFr; apply Permutation_refl|].
split; [cbn [hpeakR]; lia|].
split; [change (blocks_bytes (set_fs f S0)) with (blocks_bytes S0); unfold prh_held; cbn; lia|].
split; [reflexivity|].
split; [reflexivity|].
(* THE FREE ORDER (the kit's cut, FREEORD-NONE): nothing was allocated, so the order list of the zeroed node is [] at
   every depth (VrdNum.vrd_zero_fo), and the model's list is the leaf's of the empty trace *)
split.
{ intros _ n _. exists []. split.
  - destruct HNODE as (Hv4 & Hv8 & (Hv8' & Hrwv) & Hz & _ & Hamv & Hown & _).
    apply vrd_zero_fo.
    + split; [exact Hv8'|]. intros x Hx. apply (writable_at_grows segs _ _ x HG). exact (Hrwv x Hx).
    + unfold pj_zeroR in Hz |- *. apply (vrd_garr8_kept_on W mem1); [|exact Hz].
      intros a Ha. cbn [length repeat] in Ha.
      destruct (Hown a ltac:(cbn in Ha; lia)) as [_ Hnw].
      unfold amem_range in Hamv. apply HK; cbn in Ha; lia.
  - cbn [map]. rewrite HFL, HJV. reflexivity. }
split.
{ destruct HIN as (Vq & Vq8 & Vq16 & Hrw & _ & _ & _ & Hp'r & _ & _ & _ & Hd).
  exists p', (Z.of_nat d). split; [lia|]. split; [lia|].
  split; [eapply val_mem_kept; [|exact Vq]; intros kk Hk; cbn in Hk; apply KHI; lia|].
  split; [eapply val_mem_kept; [|exact Vq8]; intros kk Hk; cbn in Hk; apply KHI; lia|].
  split; [eapply val_mem_kept; [|exact Vq16]; intros kk Hk; cbn in Hk; apply KHI; lia|].
  intros x Hx. apply (writable_at_grows segs _ _ x HG). exact (Hrw x Hx). }
destruct HNODE as (Hv4 & Hv8 & (Hv8' & Hrwv) & Hz & _ & Hamv & Hown & _).
apply vrd_zero_fd.
- split; [exact Hv8'|]. intros x Hx. apply (writable_at_grows segs _ _ x HG). exact (Hrwv x Hx).
- unfold pj_zeroR in Hz |- *. apply (vrd_garr8_kept_on W mem1); [|exact Hz].
  intros a Ha. cbn [length repeat] in Ha.
  destruct (Hown a ltac:(cbn in Ha; lia)) as [_ Hnw].
  unfold amem_range in Hamv. apply HK; cbn in Ha; lia.
Qed.

(* ---- the early refusals at the SHARED JOIN (row 225): vrd_num_ref_early, then rows 326..328 (VrdNum.vrd_ref_join)
   with the result's shadow frame (VrdNum.vrd_pv_post_sh_frame, its parameter facts from the dispatch body). The
   conclusion is vrd_num_a_stmt's own. ---- *)
(* the generic-invariant twin: rows 326..328 by VrdRefJoinP.vrd_ref_join_P (a Theorem Labs lane's one copy of the refusal
   join with P), P of the memory at the early refusal to P of the memory at the join *)
Lemma vrd_num_early_epi_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own (W : world segs) (c : config),
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  vrd_num326_a ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own W c ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c
    (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
       vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
         (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv)
         W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c H_pst_img H326 HPM.
pose proof H326 as (pos & p' & k1 & k & ly & S & Hp & regs1 & mem1 & md1 & regs & mem & md & _ & _ & _ & _ & _ & HB &
  _).
pose proof HB as (_ & _ & _ & HJ1 & _ & _ & _ & _ & _ & HFW & _ & _ & _ & _ & _ & _ & _ &
  HIN & _ & HNODE & _ & Hq0 & Hq1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big2 d) as HSTK.
destruct HFW as (He0 & _ & _ & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTACK & _).
destruct HSTACK as (_ & _ & Hclo & Hlo & Hhi & H47 & _).
destruct HNODE as (Hv4 & _ & _ & _ & _ & Hamv & _).
destruct HIN as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _ & _ & _).
destruct HSRC as (_ & _ & _ & Hamt & _). rewrite Hlen in Hamt.
destruct (vrd_num_ref_early ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c H_pst_img H326) as [pos' Href].
eapply SRr_mono.
- refine (vrd_ref_join_P B ARx SK LAWS P PLAW d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos' (-1) _ W c _ Href HPM).
  apply (vrd_pv_post_sh_frame B ARx LAWS); [exact H_pst_img | lia | lia | lia | exact Hamv | exact Hamt].
- intros W' c' _ (H & HP'). split; [exists fx, pos', (-1); exact H | exact HP'].
Qed.

(* the old statement, byte-identical: vrd_num_early_epi_P at P := fun _ => True *)
Lemma vrd_num_early_epi : forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own (W : world segs) (c : config),
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  vrd_num326_a ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own W c ->
  SRr segs W c
    (fun W' c' => exists (fx2 : YK11.FPState) (pos rv : Z),
       vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
         (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv)
         W' c').
Proof.
intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c H_pst_img H326.
eapply SRr_mono.
- exact (vrd_num_early_epi_P (fun _ => True) (srr_inv_laws_true segs) ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v
    text len p d tb Lam peak cnt fail ran most own W c H_pst_img H326 I).
- intros W' c' _ (H & _). exact H.
Qed.

(* ---- THE ASSEMBLY of the number arm (VrdNum.vrd_num_a_stmt) with the tail as ONE named hypothesis: H_vrd_num_tail is
   the step from VnumE / VnumF's boundary vrd_num266_a (row 267) to the shared join, stated as vrd_num_a_stmt's own
   conclusion; the dispatch's two outcomes are vrd_num_scan_disp's, the early refusals close by vrd_num_early_epi.
   The tail lemma is VrdNumTail.vrd_num_tail_P (at P), so the arm is VrdNumA.vrd_num_a_P; the old vrd_num_a (no P) is
   gone with the every-state memnorm hypothesis, and vrd_num_a_from_tail below survives as the corollary at
   P := fun _ => True. ---- *)
(* the generic-invariant twin of the assembly, at ONE invariant P with its runner laws: the tail is a premise at that
   P (VrdNumTail.vrd_num_tail_P supplies it at any P with the three laws), the conclusion is VrdNum.vrd_num_a_stmt_at
   at P; VrdNumA.vrd_num_a_P closes it over every P. The text's hull budget at S0 goes to the tail, which pays the
   row-270 malloc from it; the early refusals call no allocator and use none of it *)
Lemma vrd_num_a_from_tail_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  (forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
     (W : world segs) (c : config),
   tfuzz_malloc_specX B ARx SK ->
   vrd_num266_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
     most own W c ->
   PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
   P (ms_mem (cfg_ms c)) ->
   SRr segs W c
     (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
        vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
          (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv) W' c') /\
        P (ms_mem (cfg_ms c')))) ->
  vrd_num_a_stmt_at B ARx SK P.
Proof.
intros P PLAW H_pst_img H_vrd_num_tail.
unfold vrd_num_a_stmt_at.
intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c HMAL HPRE R10q R11v HRD HDISP HBUD HARM HPM.
eapply SRr_bind.
- exact (vrd_num_scan_disp_P P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt
    fail ran most own W c HPRE R10q R11v HRD HDISP HARM HPM).
- intros W' c' _ ([H266 | H326] & HPM').
  + exact (H_vrd_num_tail ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
      most own W' c' HMAL H266 HBUD HPM').
  + exact (vrd_num_early_epi_P P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt
      fail ran most own W' c' H_pst_img H326 HPM').
Qed.

(* the old statement, byte-identical: vrd_num_a_from_tail_P at P := fun _ => True *)
Lemma vrd_num_a_from_tail :
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  (forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
     (W : world segs) (c : config),
   tfuzz_malloc_specX B ARx SK ->
   vrd_num266_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
     most own W c ->
   PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
   SRr segs W c
     (fun W' c' => exists (fx2 : YK11.FPState) (pos rv : Z),
        vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
          (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv) W' c')) ->
  vrd_num_a_stmt B ARx SK.
Proof.
intros H_pst_img H_vrd_num_tail.
assert (HT : vrd_num_a_stmt_at B ARx SK (fun _ => True)).
{ apply (vrd_num_a_from_tail_P (fun _ => True) (srr_inv_laws_true segs) H_pst_img).
  intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own W c
    HMAL H266 HBUD _.
  eapply SRr_mono; [exact (H_vrd_num_tail ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak
    cnt fail ran most own W c HMAL H266 HBUD) |].
  intros W' c' _ H. exact (conj H I). }
unfold vrd_num_a_stmt.
intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c HMAL HPRE R10q R11v HRD HDISP HBUD HARM.
eapply SRr_mono; [exact (HT ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c HMAL HPRE R10q R11v HRD HDISP HBUD HARM I) |].
intros W' c' _ (H & _). exact H.
Qed.

End s.
