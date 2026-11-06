From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma da_addr : forall c (i : nat), (i < 16)%nat ->
  Z_to_bv 64 (c + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 6)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 3))) + 72)
  = Z_to_bv 64 (c + 72 + 56 * Z.of_nat i).
Proof.
  intros c i Hi. rewrite (unsigned_lit (Z.of_nat i)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. change (2^3) with 8.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma rw_cells_same_bytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf' | rewrite Eb; exact Hb]|].
  rewrite Es. exact Hw.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecTail answer_c rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require snprintf_c rec_calls_free rec_shape_of_c.

Lemma stk_norm : forall mem lo hi, 2 ^ 20 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs mem a) -> stk rsegs (normalize rsegs mem) lo hi.
Proof.
  intros mem lo hi Hlo Hhi HW. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (writable_hi_present mem a ltac:(lia) (HW a Ha)) as [bb E].
  assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
  unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity].
Qed.

Ltac pres_tac X :=
  intros rr Hrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Lemma rec_area_glob : forall a, rec_area a -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia. Qed.

Definition rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma rom_chk_at : forall a bs i, rom_chk a bs = true -> (i < length bs)%nat ->
  ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros a bs i C Hi. unfold rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv]. split; [exact Cr|].
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma rom_chk_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  rom_chk a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (rom_chk_at a bs i C Hi) as [Cr Cv]. unfold wa. rewrite (RA _ Cr). exact Cv.
Qed.

Lemma ro_agree_of_inv : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m MI x Hx. unfold mrd. destruct (m x) as [b|] eqn:E; [|reflexivity].
  rewrite (MI _ _ E) in Hx. discriminate.
Qed.

Lemma ans_shape_chk : forall m a x, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length x) + 1 <= 2 ^ 64 ->
  rom_chk a (x ++ [Z_to_bv 8 0]) = true -> no0 x -> Z.of_nat (length x) <= LMAX -> fits x ->
  answer_c.ans_shape rsegs m a x.
Proof.
  intros m a x RA H0 H1 C N0 LX FT. pose proof (length_app x [Z_to_bv 8 0]) as LA. cbn [length] in LA.
  split; [apply rom_chk_bytes; [exact RA | lia | rewrite LA; lia | exact C]|].
  split; [exact N0|]. split; [exact LX|]. split; [exact FT|].
  intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  exact (proj1 (rom_chk_at a _ (Z.to_nat i) C ltac:(rewrite LA; lia))).
Qed.

Lemma rec_rep_O_in : forall segs gr sc L A mem R O pn, rec_rep segs gr sc L A mem R O -> In pn O -> In pn (blocks L A).
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. exact (rep_at_blocks segs _ _ _ _ _ _ pn HR (proj1 (HO pn) Hin)).
Qed.

Lemma rec_rep_keep : forall segs gr sc L A mem mem' R O,
  rec_rep segs gr sc L A mem R O ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs mem a -> writable_at segs mem' a) ->
  (forall p k i, In (p, k) O -> 0 <= i < k -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) ->
  rec_rep segs gr sc L A mem' R O.
Proof.
  intros segs gr sc L A mem mem' R O (Q & HR & HO) KG KW KB. exists Q. split; [|exact HO].
  pose proof HR as (_ & _ & _ & _ & HX & _).
  apply (rep_at_set_word segs (blocks L A) mem mem' gr sc R R Q HR eq_refl eq_refl eq_refl eq_refl).
  - intros a Ha. apply KG. unfold REC_SIZE. lia.
  - exact KW.
  - intros [p k] Hpn i Hi. exact (KB p k i (proj2 (HO (p, k)) Hpn) Hi).
  - apply (scalars_keep segs mem mem' gr R HX). intros x Hx. apply KG. unfold REC_SIZE. lia.
Qed.

Lemma rw_out : forall segs W m m' a cs, rw_cells segs m a cs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> 0 <= a + i < 2 ^ 64 /\ outside W (a + i)) -> rw_cells segs m' a cs.
Proof.
  intros segs W m m' a cs H MU HO. apply (rw_cells_transfer segs m); [exact H|]. intros i Hi.
  destruct (HO i Hi) as [R O]. split; [exact (munch_mbyte segs W m m' _ MU R O)|].
  exact (proj1 (munch_writable segs W m m' _ MU R O)).
Qed.

Lemma cells_bytes_at : forall segs m a cs, rw_cells segs m a cs -> bytes_at segs m a (cells_bytes cs).
Proof. intros segs m a cs [[_ H] _]. exact H. Qed.

Lemma bytes_cell4 : forall m a v, GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le4 v) -> rw_cells rsegs m a [C4 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le4 v)) (le4 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le4; lia | exact H].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes]. reflexivity.
  - cbn [cells_size csize]. rewrite length_le4. reflexivity.
Qed.

Lemma f18_out : forall W m m', f18_words rsegs m -> munch W m m' ->
  (forall i, 0 <= i < 8 -> outside W (snprintf_c.GOT_GUARD + i) /\ outside W (snprintf_c.GUARD + i)) ->
  f18_words rsegs m'.
Proof.
  intros W m m' [F1 (g & F2)] MU HO. split; [|exists g].
  - apply (rw_out rsegs W m m' _ _ F1 MU). intros i Hi. cbn in Hi.
    split; [unfold snprintf_c.GOT_GUARD; lia | apply (HO i ltac:(lia))].
  - apply (rw_out rsegs W m m' _ _ F2 MU). intros i Hi. cbn in Hi.
    split; [unfold snprintf_c.GUARD; lia | apply (HO i ltac:(lia))].
Qed.

Lemma ro_out : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 20 -> ro_addr rsegs (Z_to_bv 64 a) = true -> outside W a) -> ro_agree rsegs m'.
Proof.
  intros W m m' RA MU HO x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
  assert (Lx : bv_unsigned x < 2 ^ 20).
  { destruct (Z_lt_le_dec (bv_unsigned x) (2 ^ 20)) as [H|H]; [exact H|].
    rewrite <- (Z_to_bv_bv_unsigned x), ro_addr_hi in Hx by lia. discriminate. }
  assert (E : m' x = m x).
  { apply MU. apply HO; [lia|]. rewrite Z_to_bv_bv_unsigned. exact Hx. }
  unfold mrd. rewrite E. exact (RA x Hx).
Qed.

Ltac chain_tac :=
  intros rr Hrr Ho; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; cbn in Ho; first [discriminate Ho | (try split); simp_regs; reflexivity]|]);
  subst rr; cbn in Ho; first [discriminate Ho | (try split); simp_regs; reflexivity].

Lemma mod_host_shape : forall m, ro_agree rsegs m -> answer_c.ans_shape rsegs m 0x10417 REC_MOD_HOST_SHAPE.
Proof.
  intros m RA.
  assert (RO : forall i, 0 <= i <= 6 -> ro_addr rsegs (Z_to_bv 64 (0x10417 + i)) = true).
  { intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity. }
  split.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    unfold wa. rewrite (RA _ (RO (Z.of_nat i) ltac:(lia))).
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat) by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
  - split; [apply no0_nz; vm_compute; reflexivity|]. split; [cbn; unfold LMAX; lia|].
    split; [apply fits_shape_set; left; reflexivity|]. intros i Hi. apply RO. cbn in Hi. lia.
Qed.

Lemma rec_code_record : forall R fn As, r_code (rec_record R fn As) = r_code R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma stub_len : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length x) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - pose proof (inst_length x). lia.
  - rewrite rec_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Lemma stub_len2 : forall R fn As x chg, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_answer (rec_record R fn As) (fn, As) x chg)) <= Nat.max (length (inst x)) 16)%nat.
Proof.
  intros R fn As x chg H. rewrite rec_answer_text. destruct (r_refuse (rec_record R fn As) =? 0).
  - lia.
  - rewrite rec_code_record. pose proof (resp_length (r_code R) H). lia.
Qed.

Lemma room_live : forall b n, room_slots b n -> sb_live b <= sb_cap b.
Proof. intros b n (_ & H & _). lia. Qed.

Lemma rfree_b_eq : forall F bb, rfree_b bb F =
  SB (sb_live bb - Z.of_nat (length F)) (sb_bytes bb - fold_right (fun b acc => snd b + acc) 0 F) (sb_cap bb).
Proof.
  induction F as [|pn F IH]; intros bb.
  - destruct bb as [l y c]. unfold rfree_b. cbn. f_equal; lia.
  - unfold rfree_b in *. cbn [fold_left]. rewrite IH. unfold sb_free. cbn [sb_live sb_bytes sb_cap length fold_right].
    f_equal; lia.
Qed.

Lemma bsum_app : forall l1 l2 : list (Z * Z),
  fold_right (fun b acc => snd b + acc) 0 (l1 ++ l2) =
  fold_right (fun b acc => snd b + acc) 0 l1 + fold_right (fun b acc => snd b + acc) 0 l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma bsum_perm : forall l l' : list (Z * Z), Permutation l l' ->
  fold_right (fun b acc => snd b + acc) 0 l = fold_right (fun b acc => snd b + acc) 0 l'.
Proof. intros l l' Q. induction Q; cbn; lia. Qed.

Lemma rfree_shift : forall bb L A L' A' F, Permutation (blocks L A) (blocks L' A' ++ F) ->
  rfree_b bb F = sb_shift bb A A'.
Proof.
  intros bb L A L' A' F P. rewrite rfree_b_eq.
  destruct (blocks_counts L A) as (N0 & U0). destruct (blocks_counts L' A') as (N1 & U1).
  pose proof (Permutation_length P) as PL. rewrite length_app in PL.
  pose proof (bsum_perm _ _ P) as PS. rewrite bsum_app in PS.
  unfold sb_shift. f_equal; lia.
Qed.

Lemma room_down : forall b1 b k n, sb_le b1 b -> 0 <= k <= n ->
  room_slots (sb_malloc (sb_malloc b k) k) n -> room_slots (sb_malloc (sb_malloc b1 k) k) k.
Proof.
  intros b1 b k n HL Hk HR. exact (room_slots_mono _ _ k n (sb_malloc_mono _ _ k (sb_malloc_mono _ _ k HL)) Hk HR).
Qed.

Section Stub.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.

Definition sinv (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (O : list (Z * Z))
    (Lc : layout) (Ac : astate) (mc : word -> option byte) (mdc : Model) (Rc : rstate) (Oc : list (Z * Z))
    (bc : sbound) : Prop :=
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc /\
  g_rec_rep rsegs Lc Ac mc Rc Oc /\ owns_new L A O Oc /\
  (forall pn, In pn (blocks Lc Ac) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn Oc) /\
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks Lc Ac) -> In pn O) /\
  ro_agree rsegs mc /\ f18_words rsegs mc /\ res_ok_slots Ac (sb_shift bc A Ac).

Lemma sinv_init : forall K L A regs mem md R O b,
  call_pre_k B (aa_MR API) K L A regs mem md -> 0 <= K ->
  g_rec_rep rsegs L A mem R O -> ro_agree rsegs mem -> f18_words rsegs mem -> res_ok_slots A b ->
  sinv K (spZ regs) L A mem md O L A mem md R O b.
Proof.
  intros K L A regs mem md R O b PRE HK GR RA F18 RES.
  split; [exact (rjr_init B (aa_MR API) K rec_area (fun pn => In pn O) L A regs mem md PRE HK)|].
  split; [exact GR|]. split; [intros pn H; left; exact H|].
  split; [intros pn H; destruct (in_dec pair_dec pn O) as [H1|H1]; [right; exact H1 | left; split; assumption]|].
  split; [intros pn H1 H2; contradiction|]. split; [exact RA|]. split; [exact F18|].
  rewrite sb_shift_refl. exact RES.
Qed.

Lemma sinv_out : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc W,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ rec_area a -> outside W a.
Proof.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc W _ HW a Ra H1 H2.
  destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction.
Qed.

Lemma sinv_blk_out : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc W,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> 0 <= q + i < 2 ^ 64 /\ outside W (q + i).
Proof using SEGS AX.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc W SI HW q k i Hin Hi.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  destruct (block_facts B _ LAWS Lc Ac mc mdc q k i HM Hin Hi) as (_ & H4 & H5 & _).
  split; [lia|]. apply (sinv_out K S L A mem md O Lc Ac mc mdc Rc Oc bc W SI HW); [lia | lia |].
  intros Hr. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
  apply (ax_blocks_img AX Lc Ac mc mdc p k' i HM Hp Hi). apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr).
Qed.

Lemma sinv_munch_core : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W Rc',
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  g_rec_rep rsegs Lc Ac m' Rc' Oc ->
  sinv K S L A mem md O Lc Ac m' mdc Rc' Oc bc.
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W Rc' SI MU WM HW GR'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & _ & _ & HL & _).
  pose proof (sinv_out K S L A mem md O Lc Ac mc mdc Rc Oc bc W SI HW) as OUT.
  pose proof (sinv_blk_out K S L A mem md O Lc Ac mc mdc Rc Oc bc W SI HW) as BO.
  split.
  { apply (rjr_munch B (aa_MR API) SEGS LAWS K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc m' W RJ MU);
      [rewrite SEGS; exact WM | | | | |].
    - intros a Ra Hn _. exact (HW a Ra Hn).
    - intros a Ra Hn Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho) as Hlo.
      destruct (HW a Ra Hn) as [H|H]; [lia|].
      exact (GOWN Lc Ac mc mdc a HM (glob_in a (rec_area_glob a H)) Ho).
    - intros a Ha. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a ltac:(lia) H) as [H'|H'];
        [lia | apply rec_area_glob in H'; unfold GLOB_LO, GLOB_N in H'; lia].
    - intros p n i Hin Hg Hi.
      pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p n RJ Hin Hg) as Hc.
      rewrite <- (ptr_addr_stable A L Lc p n HWA Hin HL).
      apply (BO (ptr_addr Lc p) n i); [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi].
    - intros p n i Hc Hi. destruct (mr_blocks B _ LAWS Lc Ac mc mdc p n i HM Hc Hi) as (Hp & _).
      destruct (BO (ptr_addr Lc p) n i) as [Rr Oo]; [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi|].
      exact (munch_present W mc m' _ MU Rr Oo Hp). }
  split; [exact GR'|]. split; [exact ON|]. split; [exact B1|]. split; [exact B2|].
  split.
  { apply (ro_out W mc m' RA MU). intros a Ha Hro. apply OUT; [lia | lia |].
    intros Hr. rewrite glob_ro_false in Hro by exact (rec_area_glob a Hr). discriminate. }
  split; [|exact RS].
  apply (f18_out W mc m' F18 MU). intros i Hi.
  split; (apply OUT; unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia).
Qed.

Lemma sinv_kept : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc -> munch W mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall p k i, In (p, k) Oc -> 0 <= i < k -> mbyte rsegs m' (p + i) = mbyte rsegs mc (p + i).
Proof using SEGS AX.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU HW p k i Hin Hi.
  pose proof SI as (_ & GR & _).
  destruct (sinv_blk_out K S L A mem md O Lc Ac mc mdc Rc Oc bc W SI HW p k i (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) Hi)
    as [Rr Oo].
  exact (munch_mbyte rsegs W mc m' _ MU Rr Oo).
Qed.

Lemma sinv_stack : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S) ->
  sinv K S L A mem md O Lc Ac m' mdc Rc Oc bc.
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU WM HW.
  assert (HW' : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a)
    by (intros a Ra Hn; left; exact (HW a Ra Hn)).
  pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  apply (sinv_munch_core K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W Rc SI MU WM HW').
  unfold g_rec_rep in *. apply (rec_rep_keep rsegs G_REC REC_SC Lc Ac mc m' Rc Oc GR).
  - intros a Ha. apply (munch_mbyte rsegs W mc m'); [exact MU | unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia|].
    destruct (outside_dec W a) as [H|H]; [exact H|]. pose proof (HW a ltac:(unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia) H).
    unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha. lia.
  - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
  - exact (sinv_kept K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU HW').
Qed.

Lemma sinv_record_lt : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W fn,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  (length (r_calls Rc) < 16)%nat -> 0 <= fn < REC_FN_COUNT ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     S - K <= a < S \/ 0x33d50 <= a < 0x33d54 \/
     0x33d58 + 56 * Z.of_nat (length (r_calls Rc)) <= a < 0x33d58 + 56 * Z.of_nat (length (r_calls Rc)) + 8) ->
  rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls Rc)) + 1))] ->
  rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat (length (r_calls Rc))) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
  sinv K S L A mem md O Lc Ac m' mdc (rec_record Rc fn []) Oc bc.
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W fn SI Hn Hfn MU WM HW NC EN.
  set (n := length (r_calls Rc)) in *.
  assert (HW' : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a).
  { intros a Ra Hm. destruct (HW a Ra Hm) as [H|[H|H]]; [left; exact H | right | right];
      unfold rec_area, G_REC, REC_SIZE; right; lia. }
  pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  apply (sinv_munch_core K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W _ SI MU WM HW').
  unfold g_rec_rep in *.
  apply cells_bytes_at in NC. apply cells_bytes_at in EN.
  cbn [cells_bytes cbytes] in NC, EN. rewrite app_nil_r in NC, EN.
  apply bytes_at_app in EN as [EF EA]. rewrite length_le4 in EA.
  apply (rec_rep_record_lt rsegs G_REC REC_SC Lc Ac mc m' Rc Oc fn GR Hn Hfn).
  - exact NC.
  - rewrite (rec_entry_lt G_REC REC_SC Rc Hn).
    match goal with |- bytes_at _ _ ?a _ => replace a with (0x33d58 + 56 * Z.of_nat n)
      by (unfold G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_FN; lia) end. exact EF.
  - rewrite (rec_entry_lt G_REC REC_SC Rc Hn).
    match goal with |- bytes_at _ _ ?a _ => replace a with (0x33d58 + 56 * Z.of_nat n + Z.of_nat 4)
      by (unfold G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia) end. exact EA.
  - rewrite (rec_entry_lt G_REC REC_SC Rc Hn). intros a Ha H1 H2.
    apply (munch_mbyte rsegs W mc m'); [exact MU | unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia|].
    destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso.
    unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *.
    destruct (HW a ltac:(lia) H) as [H'|[H'|H']]; lia.
  - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
  - exact (sinv_kept K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU HW').
Qed.

Lemma win_out : forall (W : list (Z * Z)) S K,
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ rec_area a -> outside W a.
Proof.
  intros W S K HW a Ra H1 H2. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction.
Qed.

Lemma rjr_blk_out : forall K S O L A mem md Lc Ac mc mdc W,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> 0 <= q + i < 2 ^ 64 /\ outside W (q + i).
Proof using SEGS AX.
  intros K S O L A mem md Lc Ac mc mdc W RJ HW q k i Hin Hi.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  destruct (block_facts B _ LAWS Lc Ac mc mdc q k i HM Hin Hi) as (_ & H4 & H5 & _).
  split; [lia|]. apply (win_out W S K HW); [lia | lia |].
  intros Hr. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
  apply (ax_blocks_img AX Lc Ac mc mdc p k' i HM Hp Hi). apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr).
Qed.

Lemma rjr_win : forall K S O L A mem md Lc Ac mc mdc m' W,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac m' mdc.
Proof using SEGS AX GOWN.
  intros K S O L A mem md Lc Ac mc mdc m' W RJ MU WM HW.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & _ & _ & HL & _).
  pose proof (rjr_blk_out K S O L A mem md Lc Ac mc mdc W RJ HW) as BO.
  apply (rjr_munch B (aa_MR API) SEGS LAWS K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc m' W RJ MU);
    [rewrite SEGS; exact WM | | | | |].
  - intros a Ra Hn _. exact (HW a Ra Hn).
  - intros a Ra Hn Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho) as Hlo.
    destruct (HW a Ra Hn) as [H|H]; [lia|].
    exact (GOWN Lc Ac mc mdc a HM (glob_in a (rec_area_glob a H)) Ho).
  - intros a Ha. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a ltac:(lia) H) as [H'|H'];
      [lia | apply rec_area_glob in H'; unfold GLOB_LO, GLOB_N in H'; lia].
  - intros p n i Hin Hg Hi.
    pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p n RJ Hin Hg) as Hc.
    rewrite <- (ptr_addr_stable A L Lc p n HWA Hin HL).
    apply (BO (ptr_addr Lc p) n i); [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi].
  - intros p n i Hc Hi. destruct (mr_blocks B _ LAWS Lc Ac mc mdc p n i HM Hc Hi) as (Hp & _).
    destruct (BO (ptr_addr Lc p) n i) as [Rr Oo]; [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi|].
    exact (munch_present W mc m' _ MU Rr Oo Hp).
Qed.

Definition rcf_post (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (O : list (Z * Z))
    (Lc : layout) (Ac : astate) (mc : word -> option byte) (Rc : rstate) (Oc : list (Z * Z)) (bc : sbound)
    (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md' /\
  (exists Q, rep_at rsegs (blocks Lc Ac) mc G_REC REC_SC Rc Q /\ (forall pn, In pn Oc <-> In pn (lay_blocks Q)) /\
     (forall a, G_REC <= a < G_REC + REC_SIZE -> mbyte rsegs m' a = mbyte rsegs mc a) /\
     (forall pn, In pn (lay_blocks Q) -> ~ In pn (l_spill Q) -> In pn (blocks L' A') /\
        forall i, 0 <= i < snd pn -> mbyte rsegs m' (fst pn + i) = mbyte rsegs mc (fst pn + i)) /\
     (forall pn, In pn (blocks L' A') -> In pn (blocks Lc Ac) /\ ~ In pn (l_spill Q)) /\
     (forall pn, In pn (blocks Lc Ac) -> ~ In pn (blocks L' A') -> In pn (l_spill Q))) /\
  owns_new L A O Oc /\
  (forall pn, In pn (blocks Lc Ac) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn Oc) /\
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks Lc Ac) -> In pn O) /\
  ro_agree rsegs m' /\ f18_words rsegs m' /\ res_ok_slots A' (sb_shift bc A A') /\
  sb_le (sb_shift bc A A') (sb_shift bc A Ac) /\ length (r_calls Rc) = 16%nat.

Lemma sinv_record_full : forall K S L A mem md O Lc Ac mc Rc Oc bc L' A' m' md' m'' W fn,
  rcf_post K S L A mem md O Lc Ac mc Rc Oc bc L' A' m' md' ->
  0 <= fn < REC_FN_COUNT ->
  munch W m' m'' -> wmono rsegs m' m'' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ REC_SC <= a < REC_SC + 8) ->
  rw_cells rsegs m'' REC_SC [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
  exists Oc', sinv K S L A mem md O L' A' m'' md' (rec_record Rc fn []) Oc' bc.
Proof using SEGS AX GOWN.
  intros K S L A mem md O Lc Ac mc Rc Oc bc L' A' m' md' m'' W fn
    (RJ & (Q & HR & HO & KG & KB & BL1 & BL2) & ON & B1 & B2 & RA & F18 & RS & BLE & H16) Hfn MU WM HW EN.
  assert (HW' : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a).
  { intros a Ra Hm. destruct (HW a Ra Hm) as [H|H]; [left; exact H | right; left; unfold REC_SC, SC_SIZE in *; lia]. }
  pose proof (win_out W S K HW') as OUT.
  pose proof (rjr_blk_out K S O L A mem md L' A' m' md' W RJ HW') as BO.
  pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md L' A' m' md' RJ) as (HK1 & HK2 & HK3).
  assert (OUT2 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ (REC_SC <= a < REC_SC + 8) -> outside W a).
  { intros a Ra H1 H2. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction. }
  pose proof HR as (_ & _ & _ & _ & _ & (ND & _)).
  apply cells_bytes_at in EN. cbn [cells_bytes cbytes] in EN. rewrite app_nil_r in EN.
  apply bytes_at_app in EN as [EF EA]. rewrite length_le4 in EA.
  set (Q' := RLay (l_calls Q) [] (l_answer Q) (l_reply Q)).
  assert (HR' : rep_at rsegs (blocks L' A') m'' G_REC REC_SC (rec_record Rc fn []) Q').
  { apply (rep_at_record_full rsegs G_REC REC_SC (blocks Lc Ac) (blocks L' A') mc m'' Rc Q fn HR H16 Hfn).
    - unfold CALL_OFF_FN. rewrite Z.add_0_r. exact EF.
    - unfold CALL_OFF_NARGS. exact EA.
    - intros a Ha. rewrite <- (KG a Ha). apply (munch_mbyte rsegs W m' m'' a MU); [unfold G_REC, REC_SIZE in Ha; lia|].
      apply OUT2; unfold G_REC, REC_SIZE, REC_SC in *; lia.
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros pn Hin Hs. destruct (KB pn Hin Hs) as [Hb Hk]. split; [exact Hb|]. intros i Hi.
      destruct pn as [p k]. cbn [fst snd] in *. destruct (BO p k i Hb Hi) as [Rr Oo].
      rewrite (munch_mbyte rsegs W m' m'' _ MU Rr Oo). exact (Hk i Hi). }
  exists (lay_blocks Q').
  split; [exact (rjr_win K S O L A mem md L' A' m' md' m'' W RJ MU WM HW')|].
  split; [exists Q'; split; [exact HR' | tauto]|].
  split; [intros pn Hpn; apply ON; apply HO; exact (proj1 (proj1 (lay_drop_spill Q pn ND) Hpn))|].
  split.
  { intros pn Hpn. destruct (BL1 pn Hpn) as [Hc Hs]. destruct (B1 pn Hc) as [H|H]; [left; exact H|].
    right. apply (lay_drop_spill Q pn ND). split; [apply HO; exact H | exact Hs]. }
  split.
  { intros pn H1 H2. destruct (in_dec pair_dec pn (blocks Lc Ac)) as [Hc|Hc]; [|exact (B2 pn H1 Hc)].
    pose proof (BL2 pn Hc H2) as Hs.
    assert (Ho : In pn Oc) by (apply HO; unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hs).
    destruct (ON pn Ho) as [H|H]; [exact H | contradiction]. }
  split.
  { apply (ro_out W m' m'' RA MU). intros a Ha Hro. apply OUT2; [lia | lia |].
    intros Hr. rewrite glob_ro_false in Hro by (unfold GLOB_LO, GLOB_N, REC_SC in *; lia). discriminate. }
  split; [|exact RS].
  apply (f18_out W m' m'' F18 MU). intros i Hi.
  split; (apply OUT2; unfold REC_SC, snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia).
Qed.

Lemma freed_one : forall P : list (Z * Z), (forall pn, In pn P -> fst pn <> 0) -> freed [P] = P.
Proof.
  intros P H. unfold freed. cbn [concat]. rewrite app_nil_r.
  induction P as [|pn P IH]; [reflexivity|]. cbn [List.filter].
  rewrite (proj2 (Z.eqb_neq _ _) (H pn (or_introl eq_refl))). cbn [negb]. f_equal.
  apply IH. intros q Hq. apply H. right. exact Hq.
Qed.

Lemma count_disj : forall (l : list (Z * Z)) x, pairwise ranges_disjoint l -> 0 < snd x ->
  (count_occ pair_dec l x <= 1)%nat.
Proof.
  induction l as [|y l IH]; intros x HP Hx; cbn [count_occ]; [lia|].
  destruct HP as [H1 H2]. destruct (pair_dec y x) as [E|E].
  - subst y. assert (C0 : count_occ pair_dec l x = 0%nat).
    { destruct (count_occ pair_dec l x) eqn:C; [reflexivity|]. exfalso.
      assert (Hin : In x l) by (apply (count_occ_In pair_dec); lia).
      pose proof (H1 x Hin) as D. unfold ranges_disjoint in D. lia. }
    lia.
  - exact (IH x H2 Hx).
Qed.

Lemma perm_not_both : forall (bl bl' P : list (Z * Z)) pn, Permutation bl (bl' ++ P) ->
  pairwise ranges_disjoint bl -> 0 < snd pn -> In pn bl' -> In pn P -> False.
Proof.
  intros bl bl' P pn HP HD Hs H1 H2.
  pose proof (count_disj bl pn HD Hs) as C. rewrite (proj1 (Permutation_count_occ pair_dec _ _) HP), count_occ_app in C.
  apply (count_occ_In pair_dec) in H1. apply (count_occ_In pair_dec) in H2. lia.
Qed.

Lemma cell4_same : forall segs m m' a w, rw_cells segs m a [C4 w] -> rw_cells segs m' a [C4 w] ->
  forall i, 0 <= i < 4 -> mbyte segs m' (a + i) = mbyte segs m (a + i).
Proof.
  intros segs m m' a w H H' i Hi.
  apply cells_bytes_at in H. apply cells_bytes_at in H'. cbn [cells_bytes cbytes] in H, H'.
  rewrite app_nil_r in H, H'. destruct H as (_ & _ & H). destruct H' as (_ & _ & H').
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  change (mrd segs m' (wa (a + Z.of_nat (Z.to_nat i))) = mrd segs m (wa (a + Z.of_nat (Z.to_nat i)))).
  rewrite H, H' by (rewrite length_le4; lia). reflexivity.
Qed.

Lemma sinv_arg : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k,
  sinv K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc Ec L' A' regs' m' md' ->
  (forall a, Ec a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8 \/
     p <= a < p + k) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinv K S L A mem md O L' A' m' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k
    SI H6 HLO HHI POST HEc Hp0 FB (b1 & b2 & EB' & EB) UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  pose proof FB as (FB1 & FB2 & FB3).
  assert (HN : (length (r_calls Rp) <= 16)%nat).
  { pose proof GR as (Q0 & (_ & (C1 & _) & _) & _). unfold rec_record in C1.
    destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E; [apply Nat.ltb_lt in E; lia | exact C1]. }
  assert (ER : REC_SC <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. lia. }
  set (e := rec_entry G_REC REC_SC Rp) in *.
  assert (Hk : 0 < k) by lia.
  assert (PIN : In (p, k) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, k)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, k) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, k) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hk H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, k) pn Hpn). }
  assert (APT : forall lo n, 0 < n -> (forall a, lo <= a < lo + n -> in_img B a) -> iv_apart p k lo n).
  { intros lo n Hn HI. unfold iv_apart. destruct (Z_le_gt_dec (p + k) lo) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (lo + n) p) as [H'|H']; [right; exact H'|]. exfalso.
    apply (FB3 (Z.max p lo - p)); [lia|]. replace (p + (Z.max p lo - p)) with (Z.max p lo) by lia. apply HI. lia. }
  assert (RIMG' : forall a, REC_SC <= a < G_REC + REC_SIZE -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
    by (intros a Ha; unfold REC_SC, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia).
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c Ec (fun _ => False)
             L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. destruct (HEc a Ha) as [H|[H|H]].
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS in *. split; lia.
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_ARGS in *. split; lia.
      + exfalso. destruct Hf as [Hf|(Hi & _)]; [lia|].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hi.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn. exfalso. exact (Hn (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (NQ : ~ In p (map fst Oc)).
  { intros Hq. apply in_map_iff in Hq as ([q k'] & Eq & Hq). cbn in Eq. subst q.
    pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) as Hb.
    pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hk'. cbn in Hk'.
    pose proof (blocks_same_addr B _ LAWS L' A' m' md' p k k' PM PIN (CUR _ Hb) Hk Hk') as <-.
    exact (NOTC Hb). }
  assert (GR' : g_rec_rep rsegs L' A' m' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)])).
  { unfold g_rec_rep in *.
    apply (rec_rep_arg rsegs G_REC REC_SC Lc Ac mc L' A' m' Rp fn As Oc x p k GR H6 BN BS).
    - intros a Ha N1 N2.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (apply RIMG'; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      assert (NE : ~ Ec a).
      { intros HE. destruct (HEc a HE) as [H|[H|H]]; [contradiction | contradiction |].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
      exact (proj1 (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                       NS NE)).
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros pn Hpn. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn) as Hb.
      split; [exact (CUR pn Hb)|]. intros i Hi. destruct pn as [q n]. cbn [fst snd] in *.
      exact (BK q n i Hb (fun H => H) Hi).
    - exact NQ.
    - exact Hp0.
    - exact PIN.
    - exact Hno.
    - exact Hlx.
    - exact Hsz.
    - exact BX.
    - apply APT; [unfold REC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - apply APT; [unfold SC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia. }
  split; [exact RJ'|]. split; [exact GR'|].
  split.
  { intros pn Hpn. apply in_app_or in Hpn as [H|[<-|[]]]; [exact (ON pn H)|].
    destruct (in_dec pair_dec (p, k) O) as [H|H]; [left; exact H | right; intros Hb].
    destruct (in_dec pair_dec (p, k) (blocks Lc Ac)) as [Hc|Hc]; [exact (NOTC Hc) | exact (H (B2 _ Hb Hc))]. }
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X].
    - subst pn. right. apply in_or_app. right. left. reflexivity.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; apply in_or_app; left; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|]. split; [exact F18'|].
  rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p k EB' EB).
  exact RS'.
Qed.

Lemma sinv_sarg : forall K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c L' A' regs' m' md' m'' W x p k,
  sinv K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc (fun a => p <= a < p + k) L' A' regs' m' md' ->
  munch W m' m'' -> wmono rsegs m' m'' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m'' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m'' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinv K S L A mem md O L' A' m'' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c L' A' regs' m' md' m'' W x p k
    SI H6 HLO HHI POST MU WM HW Hp0 FB EBS UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _).
  assert (HN : (length (r_calls Rp) <= 16)%nat).
  { pose proof GR as (Q0 & (_ & (C1 & _) & _) & _). unfold rec_record in C1.
    destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E; [apply Nat.ltb_lt in E; lia | exact C1]. }
  assert (ER : REC_SC <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. lia. }
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> rec_area a).
  { intros a Ra Hn. destruct (HW a Ra Hn) as [H|H];
      unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ rec_area a -> outside W a).
  { intros a Ra Hr. destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso. exact (Hr (HWR a Ra H)). }
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in PF, PK, PS.
  assert (BLW : forall q n i, In (q, n) (user_blocks A') -> 0 <= i < n ->
            0 <= ptr_addr L' q + i < 2 ^ 64 /\ outside W (ptr_addr L' q + i)).
  { intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m' md' q n i PM Hin Hi) as (Q1 & Q2 & Q3 & _).
    split; [lia|]. apply OUTW; [lia|]. intros Hr. apply (ax_blocks_img AX L' A' m' md' q n i PM Hin Hi).
    apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr). }
  assert (PM2 : aa_MR API L' A' m'' md').
  { apply (mr_keep B _ LAWS L' A' m' m'' md' W PM MU).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a PM Ho) as [Hl1 Hl2].
      apply OUTW; [lia|]. intros Hr. exact (GOWN L' A' m' md' a PM (glob_in a (rec_area_glob a Hr)) Ho).
    - intros q n i Hin Hi. exact (proj2 (BLW q n i Hin Hi)). }
  assert (POST2 : call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc
                    (fun a => p <= a < p + k \/ (0 <= a < 2 ^ 64 /\ ~ outside W a)) L' A' regs' m'' md').
  { split; [exact PM2|]. split; [exact PW|]. split; [exact PB|]. split; [exact PL|]. split; [exact PA|].
    split; [exact PR|]. split; [exact PV|]. rewrite SEGS.
    split.
    { intros a Hr Hn1 Hn2 Hs He.
      assert (Ra : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEGS a Hr); lia]).
      assert (Oa : outside W a).
      { destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso. apply He. right. split; assumption. }
      destruct (PF a Hr Hn1 Hn2 Hs (fun H => He (or_introl H))) as [E1 E2].
      rewrite (munch_mbyte rsegs W m' m'' a MU Ra Oa). split; [exact E1|].
      rewrite E2. exact (munch_writable rsegs W m' m'' a MU Ra Oa). }
    split.
    { intros q n i H1 H2 Hi. rewrite <- (PK q n i H1 H2 Hi). rewrite <- (PA q n H1 H2).
      destruct (BLW q n i H2 Hi) as [Rr Oo]. exact (munch_mbyte rsegs W m' m'' _ MU Rr Oo). }
    intros a Hs. exact (WM _ (PS a Hs)). }
  pose proof FB as (FB1 & FB2 & FB3).
  pose proof (bytes_at_bound _ _ _ _ BX) as BXB. rewrite length_app in BXB. cbn [length] in BXB.
  apply (sinv_arg K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c _ L' A' regs' m'' md' x p k
           SI H6 HLO HHI POST2).
  - intros a [Ha|(Ra & Ha)]; [right; right; exact Ha|].
    destruct (HW a Ra Ha) as [H|H]; [left; exact H | right; left; exact H].
  - exact Hp0.
  - exact FB.
  - exact EBS.
  - exact UB.
  - unfold blocks_kept in *. rewrite SEGS in BK |- *. intros a0 k0 i Hin Hg Hi.
    rewrite <- (BK a0 k0 i Hin Hg Hi).
    destruct (sinv_blk_out K S L A mem md O Lc Ac mc mdc _ Oc bc W SI
                (fun a Ra Hn => or_intror (HWR a Ra Hn)) a0 k0 i Hin Hi) as [Rr Oo].
    exact (munch_mbyte rsegs W m' m'' _ MU Rr Oo).
  - exact RGN.
  - exact BN.
  - exact BS.
  - apply (bytes_at_transfer rsegs m' m'' p _ BX). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (munch_mbyte rsegs W m' m'' _ MU); [lia|]. apply OUTW; [lia|]. intros Hr.
    apply (FB3 i); [lia|]. apply (glob_in_img B SEGS). exact (rec_area_glob _ Hr).
  - exact Hno.
  - exact Hlx.
  - exact Hsz.
  - exact INI.
  - exact RS'.
  - apply (ro_out W m' m'' RA' MU). intros a Ha Hro. apply OUTW; [lia|].
    intros Hr. rewrite glob_ro_false in Hro by exact (rec_area_glob a Hr). discriminate.
  - apply (f18_out W m' m'' F18' MU). intros i Hi.
    split; (apply OUTW; unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia).
Qed.

Lemma post_k_keep_hi : forall Kc L A regs mem md E L' A' regs' mem' md' a,
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) Kc L A regs mem md E L' A' regs' mem' md' ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - Kc <= a < spZ regs) -> ~ E a ->
  mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a).
Proof using SEGS ERRNO_LOW.
  intros Kc L A regs mem md E L' A' regs' mem' md' a HM POST Ha Hs He.
  pose proof (aa_laws API) as LAWS.
  pose proof POST as (PM & _ & _ & _ & _ & _ & _ & PF & _). rewrite SEGS in PF.
  apply PF; [left; exact Ha | intros Ho; pose proof (mr_owned_low B _ LAWS L A mem md a HM Ho); lia
            | intros Ho; pose proof (mr_owned_low B _ LAWS L' A' mem' md' a PM Ho); lia
            | unfold scratch_k; intros [H|H]; [exact (Hs H) | lia] | exact He].
Qed.

Hypothesis RCF : rec_calls_free_contract B API.

Lemma sinv_rcf : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c (P : config -> Prop),
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc -> length (r_calls Rc) = 16%nat ->
  getr regs_c 10 = Z_to_bv 64 REC_SC -> getr regs_c 11 = Z_to_bv 64 1 ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> S - K <= spZ regs_c - RCF_K -> spZ regs_c <= S ->
  getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  (forall L' A' regs' m' md', regs_preserved regs_c regs' ->
     rcf_post K S L A mem md O Lc Ac mc Rc Oc bc L' A' m' md' ->
     (forall a, spZ regs_c <= a < S ->
        mbyte rsegs m' a = mbyte rsegs mc a /\ (writable_at rsegs mc a -> writable_at rsegs m' a)) ->
     SR rsegs (mkCfg (mkst regs' (getr regs_c 1) m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs_c (Z_to_bv 64 REC_CALLS_FREE) mc (seg_rom rsegs)) mdc) P.
Proof using SEGS AX GOWN GOTG GRD ERRNO_LOW RCF.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c P SI H16 A10 A11 HRA HAL HLO HHI HTP KONT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & HWc & HBd & HL & HLen & HV & _ & _ & _ & HF & HRM & HKP & HSC & HAX).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  pose proof GR as (Q & HR & HO).
  pose proof HR as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & HA & HP & HX & (ND & HAP)).
  pose proof G5 as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7).
  assert (SPB : alloc_ceiling + 8192 + 64 <= spZ regs_c) by (unfold RCF_K, ALLOC_STACK in HLO; lia).
  assert (NZS : forall pn, In pn (l_spill Q) -> fst pn <> 0 /\ 0 < snd pn /\ In pn (blocks Lc Ac)).
  { intros pn Hpn. apply In_nth_error in Hpn as (k & Ek).
    assert (Hk : (k < length (snd (r_spill Rc)))%nat) by (rewrite <- CF3; apply nth_error_Some; rewrite Ek; discriminate).
    destruct (nth_error (snd (r_spill Rc)) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (CF7 k s pn Es Ek) as (_ & NZ & IN & SZ & _). split; [exact NZ|]. split; [lia | exact IN]. }
  destruct (l_spill Q) as [|pn0 ps0] eqn:EP.
  - assert (E0 : snd (r_spill Rc) = []) by (apply length_zero_iff_nil; rewrite <- CF3; reflexivity).
    rewrite E0 in CF5. cbn [length Z.of_nat] in CF5.
    assert (NF : rw_cells rsegs mc (REC_SC + 4) [C4 (Z_to_bv 64 0)]).
    { apply bytes_cell4; [unfold REC_SC, GLOB_LO; lia | unfold REC_SC, GLOB_LO, GLOB_N; lia | exact CF5]. }
    set (sw := reg_get regs_c 2) in *.
    change (spZ regs_c) with (bv_unsigned sw) in *.
    pose proof (bv_unsigned_in_range 64 sw) as RSW. unfold bv_modulus in RSW.
    destruct (present_rw_cells rsegs mc (bv_unsigned sw + -64) 64 ltac:(lia) ltac:(lia)) as [junk FR0].
    { intros i Hi. apply (writable_hi_present mc); [lia|]. rewrite <- SEGS. apply HSC. left.
      unfold RCF_K, ALLOC_STACK in HLO. lia. }
    assert (NFA : rec_calls_free.nfa (Z_to_bv 64 REC_SC) 0 = REC_SC + 4)
      by (unfold rec_calls_free.nfa; rewrite unsigned_lit by (unfold REC_SC; lia); lia).
    set (W2 := [(bv_unsigned sw + -64, bv_unsigned sw); (REC_SC + 4, REC_SC + 4 + 4)]).
    set (Qf := fun ms : machine_state => exists m2,
      (exists y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
         ms = MS (mkR (reg_get regs_c 1) sw (reg_get regs_c 3) (reg_get regs_c 4) y5 y6 y7 (reg_get regs_c 8)
                    (reg_get regs_c 9) y10 y11 y12 y13 y14 y15 y16 y17 (reg_get regs_c 18) (reg_get regs_c 19)
                    (reg_get regs_c 20) (reg_get regs_c 21) (reg_get regs_c 22) (reg_get regs_c 23) (reg_get regs_c 24)
                    (reg_get regs_c 25) (reg_get regs_c 26) (reg_get regs_c 27) y28 y29 y30 y31)
                 fp_regs (ret_pc (reg_get regs_c 1)) fp_csr None m2 (seg_rom rsegs)) /\
      munch W2 mc m2 /\ wmono rsegs mc m2 /\ rw_cells rsegs m2 (REC_SC + 4) [C4 (Z_to_bv 64 0)]).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sw.
      assert (R10 : reg_get regs_c 10 = Z_to_bv 64 REC_SC) by exact A10.
      assert (R11 : reg_get regs_c 11 = Z_to_bv 64 (Z.of_nat 1)) by exact A11.
      rewrite R10, R11. unfold REC_CALLS_FREE.
      eapply evt_cut; [|intros ms Hms; exact Hms].
      eapply (rec_calls_free.k_pro) with (n := 1%nat) (Q := fun ms => evt rsegs Qf ms) (junk := junk);
        [lia | lia | lia | exact FR0 |].
      intros m1 FR1 MU1 WM1. unfold rec_calls_free.st_oh.
      intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y28 y29 y30 y31. cbv beta.
      assert (NF1 : rw_cells rsegs m1 (rec_calls_free.nfa (Z_to_bv 64 REC_SC) 0) [C4 (Z_to_bv 64 0)]).
      { rewrite NFA. apply (rw_out rsegs _ mc m1 _ _ NF MU1). intros i Hi. cbn in Hi.
        split; [unfold REC_SC; lia|]. cbn. split; [unfold REC_SC; lia | exact I]. }
      eapply (rec_calls_free.k_oh_last) with (i := 0%nat);
        [lia | lia | rewrite unsigned_lit by (unfold REC_SC; lia); unfold REC_SC; lia |
         rewrite unsigned_lit by (unfold REC_SC; lia); unfold REC_SC; lia | reflexivity | exact FR1 | exact NF1 |].
      intros m2 FR2 NF2 MU2 WM2. rewrite NFA in NF2, MU2. unfold rec_calls_free.st_ret.
      intros y5' y6' y7' y10' y11' y12' y13' y14' y15' y16' y17' y28' y29' y30' y31'.
      exists m2. split; [do 15 eexists; reflexivity|].
      split; [|split; [exact (wmono_trans rsegs _ _ _ WM1 WM2) | exact NF2]].
      apply (munch_trans W2 mc m1 m2).
      - apply (munch_weaken [(bv_unsigned sw + -64, bv_unsigned sw)] W2); [|exact MU1].
        intros x (Hx1 & Hx2 & _). split; [exact Hx1 | exact I].
      - apply (munch_weaken [(REC_SC + 4, REC_SC + 4 + 4)] W2); [|exact MU2].
        intros x (Hx1 & Hx2 & _). split; [exact Hx2 | exact I]. }
    intros ms' (can & (m2 & (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & ->)
      & MU2 & WM2 & NF2) & EQ).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & X).
    rewrite (ret_pc_of_ok (reg_get regs_c 1) HRA). change (reg_get regs_c 1) with (getr regs_c 1).
    assert (HW2 : forall a, 0 <= a < 2 ^ 64 -> ~ outside W2 a -> S - K <= a < S \/ rec_area a).
    { intros a Ra Hn. unfold W2 in Hn. cbn in Hn. unfold RCF_K, ALLOC_STACK in HLO.
      destruct (Z_lt_le_dec a (bv_unsigned sw + -64)) as [D|D].
      - right. left. unfold REC_SC, SC_SIZE in *. lia.
      - left. destruct (Z_lt_le_dec a (bv_unsigned sw)) as [D'|D']; [lia|]. exfalso. apply Hn.
        split; [lia|]. split; [unfold REC_SC in *; lia | exact I]. }
    assert (GR2 : g_rec_rep rsegs Lc Ac m2 Rc Oc).
    { unfold g_rec_rep in *. apply (rec_rep_keep rsegs G_REC REC_SC Lc Ac mc m2 Rc Oc GR).
      - intros a Ha. destruct (Z_lt_le_dec a (REC_SC + 4)) as [D|D];
          [|destruct (Z_lt_le_dec a (REC_SC + 8)) as [D'|D']].
        + unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in *.
          apply (munch_mbyte rsegs W2 mc m2 a MU2); [lia|]. unfold W2. cbn.
          split; [lia|]. split; [lia | exact I].
        + replace a with (REC_SC + 4 + (a - (REC_SC + 4))) by ring.
          exact (cell4_same rsegs mc m2 (REC_SC + 4) _ NF NF2 (a - (REC_SC + 4)) ltac:(lia)).
        + unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in *.
          apply (munch_mbyte rsegs W2 mc m2 a MU2); [lia|]. unfold W2. cbn.
          split; [lia|]. split; [lia | exact I].
      - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
      - exact (sinv_kept K S L A mem md O Lc Ac mc mdc Rc Oc bc m2 W2 SI MU2 HW2). }
    pose proof (sinv_munch_core K S L A mem md O Lc Ac mc mdc Rc Oc bc m2 W2 Rc SI MU2 WM2 HW2 GR2) as SI2.
    destruct SI2 as (RJ2 & _ & _ & _ & _ & RA2 & F182 & _).
    apply (KONT Lc Ac R' m2 mdc).
    + pres_tac X.
    + split; [exact RJ2|]. split.
      { exists Q. split; [exact HR|]. split; [exact HO|]. split.
        - intros a Ha. apply (munch_mbyte rsegs W2 mc m2 a MU2); [unfold G_REC, REC_SIZE in *; lia|].
          unfold W2. cbn. split; [unfold G_REC, REC_SIZE in *; lia|]. split; [unfold G_REC, REC_SC in *; lia | exact I].
        - split; [|split].
          + intros pn Hpn _. pose proof (rep_at_blocks rsegs _ _ _ _ _ _ pn HR Hpn) as Hb. split; [exact Hb|].
            intros i Hi. destruct pn as [p k]. cbn [fst snd] in *.
            exact (sinv_kept K S L A mem md O Lc Ac mc mdc Rc Oc bc m2 W2 SI MU2 HW2 p k i (proj2 (HO (p, k)) Hpn) Hi).
          + intros pn Hpn. split; [exact Hpn|]. intros Hs. rewrite EP in Hs. destruct Hs.
          + intros pn H1 H2. contradiction. }
      split; [exact ON|]. split; [exact B1|]. split; [exact B2|]. split; [exact RA2|]. split; [exact F182|].
      split; [exact RS|]. split; [apply sb_le_refl | exact H16].
    + intros a Ha. assert (Ho : outside W2 a).
      { unfold W2. cbn. split; [lia|]. split; [unfold REC_SC in *; lia | exact I]. }
      split; [exact (munch_mbyte rsegs W2 mc m2 a MU2 ltac:(lia) Ho)|].
      exact (proj1 (munch_writable rsegs W2 mc m2 a MU2 ltac:(lia) Ho)).
  - assert (IN0 : In pn0 (blocks Lc Ac)) by exact (proj2 (proj2 (NZS pn0 (or_introl eq_refl)))).
    destruct pn0 as [a0 k0].
    destruct (proj1 (YI04.blocks_In Lc Ac a0 k0) IN0) as (p0 & _ & Hp0).
    assert (INIT : st_init_done Ac = true) by exact (YI04.init_done_of_block Ac (p0, k0) HWc Hp0).
    rewrite <- EP in *.
    assert (FR1 : freed [l_spill Q] = l_spill Q) by (apply freed_one; intros pn Hpn; exact (proj1 (NZS pn Hpn))).
    pose proof RCF as RC. unfold rec_calls_free_contract in RC. rewrite SEGS in RC.
    eapply SR_bind.
    { apply (RC Lc Ac regs_c mc mdc REC_SC [l_spill Q] (sb_shift bc A Ac)).
      - apply (call_pre_k_of_rjr B _ K S rec_area _ L A mem md Lc Ac mc mdc RCF_K regs_c RJ HRA HAL);
          [unfold RCF_K, ALLOC_STACK; lia | exact HLO | exact HHI | exact HTP].
      - exact RA.
      - exact A10.
      - exact A11.
      - unfold calls_slots. split; [cbn; lia|]. intros i P0 EP0.
        destruct i as [|i]; [|destruct i; discriminate]. cbn in EP0. injection EP0 as <-.
        split; [lia|]. split.
        { rewrite CF3. replace (REC_SC + 56 * Z.of_nat 0 + 4) with (REC_SC + CALL_OFF_NARGS) by (unfold CALL_OFF_NARGS; lia).
          rewrite SEGS. exact CF5. }
        split; [intros j Hj; rewrite SEGS; apply glob_writable; unfold REC_SC, GLOB_LO, GLOB_N; lia|].
        intros a pn Hpn.
        assert (Ha : (a < length (snd (r_spill Rc)))%nat) by (rewrite <- CF3; apply nth_error_Some; rewrite Hpn; discriminate).
        destruct (nth_error (snd (r_spill Rc)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
        destruct (CF7 a s pn Es Hpn) as (BY & _ & IN & _). split; [|right; exact IN].
        replace (REC_SC + 56 * Z.of_nat 0 + 8 + 8 * Z.of_nat a) with (REC_SC + CALL_OFF_ARGS + 8 * Z.of_nat a)
          by (unfold CALL_OFF_ARGS; lia).
        rewrite SEGS. exact BY.
      - rewrite FR1. exact CF6.
      - unfold REC_SC. lia.
      - cbn. unfold REC_SC. lia.
      - intros j Hj. right. apply glob_in. cbn in Hj. unfold REC_SC, GLOB_LO, GLOB_N in *. lia.
      - exact RS. }
    intros c2 (L' & A' & R' & m' & md' & -> & POST & PERM & BK & UK & US & NA & SCK & FG & RA' & GK & INI & RGN & UNI & RES').
    rewrite FR1 in PERM, BK, UK, RES'.
    assert (EQB : rfree_b (sb_shift bc A Ac) (l_spill Q) = sb_shift bc A A')
      by (rewrite (rfree_shift (sb_shift bc A Ac) Lc Ac L' A' (l_spill Q) PERM); apply sb_shift_trans).
    pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
    unfold blocks_kept in BK. rewrite SEGS in RA', PF, FG, BK.
    assert (NAF : forall a, nargs_field REC_SC (length [l_spill Q]) a -> REC_SC + 4 <= a < REC_SC + 8).
    { intros a (i & Hi & Ha). cbn in Hi. assert (i = 0%nat) by lia. subst i. cbn in Ha. lia. }
    rewrite SEGS. apply (KONT L' A' R' m' md').
    + exact PR.
    + split.
      { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc RCF_K regs_c
                 (nargs_field REC_SC (length [l_spill Q])) (fun _ => False) L' A' R' m' md' RJ
                 (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST)).
        - exact HLO.
        - exact HHI.
        - intros a Ha _. pose proof (NAF a Ha) as H. split; [left; unfold REC_SC, SC_SIZE in *; lia | unfold REC_SC in *; lia].
        - intros p n _ _ _ [].
        - intros p n Hin Hc Hn. destruct (in_dec pair_dec (ptr_addr Lc p, n) (l_spill Q)) as [Hs|Hs].
          + assert (Ho : In (ptr_addr Lc p, n) Oc)
              by (apply HO; unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hs).
            rewrite (ptr_addr_stable A L Lc p n HWA Hin HL) in Ho.
            destruct (ON _ Ho) as [H|H]; [exact H|]. exfalso. apply H. unfold blocks. apply in_map_iff.
            exists (p, n). split; [reflexivity | exact Hin].
          + exfalso. exact (Hn (UK p n Hc Hs)).
        - exact RGN.
        - intros Hf. rewrite (INI INIT) in Hf. discriminate. }
      split.
      { exists Q. split; [exact HR|]. split; [exact HO|]. split.
        - intros a Ha. apply (FG a); [apply glob_in; unfold G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia|].
          intros Hn. pose proof (NAF a Hn). unfold G_REC, REC_SC in *. lia.
        - split; [|split].
          + apply (spill_others_kept rsegs Q (blocks Lc Ac) (blocks L' A') (l_spill Q) mc m' ND).
            * intros pn Hpn. exact (rep_at_blocks rsegs _ _ _ _ _ _ pn HR Hpn).
            * intros pn Hpn. exact Hpn.
            * intros pn Hpn. apply in_app_or. exact (Permutation_in pn PERM Hpn).
            * exact BK.
          + intros pn Hpn. split; [apply (Permutation_in pn (Permutation_sym PERM)); apply in_or_app; left; exact Hpn|].
            intros Hs. exact (perm_not_both _ _ _ pn PERM (mr_blocks_disjoint B _ LAWS Lc Ac mc mdc HM)
                                (proj1 (proj2 (NZS pn Hs))) Hpn Hs).
          + intros pn H1 H2. destruct (in_app_or _ _ _ (Permutation_in pn PERM H1)) as [H|H]; [contradiction | exact H]. }
      split; [exact ON|]. split; [exact B1|]. split; [exact B2|]. split; [exact RA'|].
      split.
      { destruct (ax_statics AX L' A' m' md' PM) as (_ & (g & Hg & HWg) & _).
        rewrite GRD, SEGS in HWg.
        apply (f18_words_after mc m' g F18); [|exact Hg | exact HWg].
        intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
      split; [rewrite <- EQB; exact RES'|]. split; [|exact H16].
      rewrite <- EQB. apply rfree_b_le. apply Forall_forall. intros pn Hpn. pose proof (NZS pn Hpn) as (_ & H & _). lia.
    + intros a Ha.
      assert (Hf : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
      assert (N1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho); lia).
      assert (N2 : ~ owned B L' A' a) by (intros Ho; pose proof (mr_owned_low B _ LAWS L' A' m' md' a PM Ho); lia).
      assert (N3 : ~ scratch_k B RCF_K regs_c a) by (unfold scratch_k; lia).
      assert (N4 : ~ nargs_field REC_SC (length [l_spill Q]) a) by (intros Hn; pose proof (NAF a Hn); unfold REC_SC in *; lia).
      destruct (PF a Hf N1 N2 N3 N4) as [E1 E2]. split; [exact E1 | exact (proj1 E2)].
Qed.

Hypothesis ANS : answer_contract B API.
Hypothesis SLACK : block_slack_present B API.

Lemma sinv_answer : forall K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre c sh e x chg,
  call_pre_t B API K L A regs mem md -> ANSWER_K <= K ->
  sinv K (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc ->
  getr regs1 1 = getr regs 1 -> spZ regs1 = spZ regs -> regs_preserved regs regs1 ->
  getr regs1 10 = Z_to_bv 64 c -> getr regs1 11 = Z_to_bv 64 sh -> chg = negb (bv_unsigned (getr regs1 12) =? 0) ->
  (r_refuse Rc = 0 -> ans_shape rsegs mc sh x) ->
  (r_refuse Rc = 0 -> chg = true -> ans_entry Rc c e) ->
  frm_zero fp_csr -> sb_le (sb_shift bc A Ac) bpre ->
  room_slots (sb_malloc (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (snd (rec_answer Rc e x chg))) + 1))
                (Z.of_nat (length (snd (rec_answer Rc e x chg))) + 1))
             (Z.of_nat (length (snd (rec_answer Rc e x chg))) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 ANSWER) mc (seg_rom rsegs)) mdc)
    (tail_ret B API K L A regs mem md O Rc e x chg bc bpre).
Proof using SEGS AX CTX ERRNO_LOW ANS SLACK.
  intros K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre c sh e x chg PRE KA SI RA1 SP1 RP1 A10 A11 ACH SH EN FRM
    BLE ROOM.
  destruct SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  rewrite <- SEGS in GR, RA, F18, SH |- *.
  exact (answer_tail B API SEGS AX CTX ERRNO_LOW ANS SLACK K L A regs mem md O Lc Ac regs1 mc mdc Rc Oc bc bpre
           (sb_shift bc A Ac) c sh e x chg
           PRE KA RJ RA1 SP1 RP1 A10 A11 ACH GR SH EN FRM F18 RA RS eq_refl BLE ROOM ON B1 B2).
Qed.

Fixpoint rs_rof (l : list (Z * Z * bool)) (a : Z) : bool :=
  match l with
  | [] => false
  | (b, z, w) :: l' => if (b <=? a) && (a + 1 <=? b + z) then negb w else rs_rof l' a
  end.

Lemma rs_ro_addr_rof : forall segs a,
  ro_addr segs a = rs_rof (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs) (bv_unsigned a).
Proof.
  intros segs a. unfold ro_addr. generalize (bv_unsigned a) as z.
  induction segs as [|sg segs IH]; intros z; [reflexivity|].
  cbn [find_segment map rs_rof]. destruct (_ && _); [reflexivity | apply IH].
Qed.

Lemma rs_rsegs_proj : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) rsegs =
  [(65536, 12288, false); (77824, 61440, false); (139264, 4096, true); (143360, 204800, true)].
Proof. vm_compute. reflexivity. Qed.

Lemma rs_ro_rsegs : forall a, 0 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = true <-> 65536 <= a < 139264.
Proof.
  intros a Ha. rewrite rs_ro_addr_rof, rs_rsegs_proj, unsigned_lit by lia. cbn [rs_rof].
  repeat match goal with |- context [?u <=? ?v] => destruct (Z.leb_spec u v) end; cbn [andb negb];
    split; intros; first [reflexivity | discriminate | lia | exfalso; lia].
Qed.

Lemma rs_bytes_pad : forall segs m a bs (k : nat), bytes_at segs m a bs ->
  a + Z.of_nat (length bs) + Z.of_nat k <= 2 ^ 64 ->
  (forall j, (j < k)%nat -> mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat j) <> None) ->
  exists sl, length sl = k /\ bytes_at segs m a (bs ++ sl).
Proof.
  intros segs m a bs k H Hk Hr.
  exists (map (fun j => match mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat j) with
                        | Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  split; [rewrite length_map, length_seq; reflexivity|].
  apply bytes_at_app. split; [exact H|].
  pose proof (bytes_at_bound _ _ _ _ H) as HB.
  split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite (map_nth_error _ _ _ (nth_error_seq_lt 0 k i Hi)). cbn [Nat.add].
  change (mrd segs m (wa (a + Z.of_nat (length bs) + Z.of_nat i)))
    with (mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat i)).
  destruct (mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat i)) eqn:E; [reflexivity | exfalso; exact (Hr i Hi E)].
Qed.

Lemma sinv_str : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p v,
  sinv K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  ro_agree rsegs mem -> NULL_LIT + 7 <= S - K ->
  str_arg B L A O S K mem p v ->
  exists s slack, 0 <= p < 2 ^ 64 /\ (if p =? 0 then NULL_LIT else p) = s /\ 0 <= s /\
    bytes_at rsegs mc s (sarg v ++ Z_to_bv 8 0 :: slack) /\ no0 (sarg v) /\ Z.of_nat (length (sarg v)) <= LMAX /\
    (- (s + Z.of_nat (length (sarg v)) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (s + Z.of_nat (length (sarg v ++ Z_to_bv 8 0 :: slack)) <= S - K \/ S <= s) /\
    str_home B Lc Ac S s (Z.of_nat (length (sarg v)) + 1) /\
    (forall a, s <= a < s + Z.of_nat (length (sarg v ++ Z_to_bv 8 0 :: slack)) -> ~ rec_area a).
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc p v SI RA HS H.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & RAc & _).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct v as [x|].
  2: { exact (sarg_src B SEGS Lc Ac O S K mc p None RAc ltac:(lia) HS H). }
  destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _ & HK & _).
  rewrite SEGS in HF, HK.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in DJ, NRA. cbn [length] in DJ, NRA.
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0
      by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (p + Z.of_nat (length x) + 1 + j) <> None).
  { intros j Hj E. pose proof BS as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (Z.of_nat (length x) + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (Z.of_nat (length x) + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))))
      with (mbyte rsegs mem (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia.
    replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (LX1 : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = Z.of_nat (length x) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (SAME : (forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)) ->
                 bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                 (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None)).
  { intros KE. split.
    - apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi. apply KE. lia.
    - intros j Hj. replace (p + Z.of_nat (length x) + 1 + j) with (p + (Z.of_nat (length x) + 1 + j)) by ring.
      rewrite KE by lia. replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) by ring.
      exact (PR0 j Hj). }
  assert (CASES : bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                  (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None) /\
                  str_home B Lc Ac S p (Z.of_nat (length x) + 1)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. refine (proj1 (HF (p + i) _ _ _ _)).
        - unfold free_a. left. lia.
        - lia.
        - lia.
        - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
      destruct (SAME KE) as [S1 S2]. split; [exact S1 | split; [exact S2 | left; lia]].
    - assert (NG : ~ In (q, k) O).
      { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
      assert (QC : In (q, k) (blocks Lc Ac)).
      { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
      pose proof Hq as Hq'. unfold blocks in Hq'. apply in_map_iff in Hq' as ([pp k'] & E & Hp). cbn [fst snd] in E.
      injection E as E1 E2. subst k'.
      split.
      { apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi.
        assert (Hng : ~ (fun pn => In pn O) (ptr_addr L pp, k)) by (intros Hg; apply NG; rewrite <- E1; exact Hg).
        pose proof (HK pp k (p + i - q) Hp Hng ltac:(lia)) as E. rewrite E1 in E.
        replace (q + (p + i - q)) with (p + i) in E by ring. exact E. }
      split.
      { intros j Hj.
        assert (PRc : present mc (p + Z.of_nat (length x) + 1 + j)).
        { destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + j) (q + k)) as [Hlt|Hge].
          - replace (p + Z.of_nat (length x) + 1 + j) with (q + (p + Z.of_nat (length x) + 1 + j - q)) by ring.
            exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q k (p + Z.of_nat (length x) + 1 + j - q) HM QC ltac:(lia))).
          - apply (SLACK Lc Ac mc mdc q k _ HM QC). split; [lia|]. Z.div_mod_to_equations. lia. }
        destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
      right. left. exists q, k. split; [exact QC | lia].
    - pose proof H3 as H3'. rewrite SEGS in H3'.
      assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi.
        assert (RO : ro_addr rsegs (Z_to_bv 64 (p + i)) = true).
        { destruct (Z_lt_ge_dec i (Z.of_nat (length x) + 1)) as [Hl|Hl]; [exact (H3' i ltac:(lia))|].
          pose proof (H3' (Z.of_nat (length x)) ltac:(lia)) as Hlast. apply rs_ro_rsegs in Hlast; [|lia].
          apply rs_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA RO). reflexivity. }
      destruct (SAME KE) as [S1 S2].
      split; [exact S1 | split; [exact S2 | right; right; split; [exact H1 | split; [exact H2 | exact H3]]]]. }
  destruct CASES as (TX & PADP & HOMEc).
  destruct (rs_bytes_pad rsegs mc p (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TX) as (sl & SL & BS').
  { rewrite LX1, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LX1. replace (p + (Z.of_nat (length x) + 1) + Z.of_nat j)
      with (p + Z.of_nat (length x) + 1 + Z.of_nat j) by ring. apply PADP. lia. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  exists p, sl. cbn [sarg].
  split; [lia|]. split; [rewrite (proj2 (Z.eqb_neq _ _) Hp0); reflexivity|]. split; [lia|].
  split; [exact BS'|]. split; [exact N0|]. split; [exact LX|].
  split; [change ((- (p + Z.of_nat (length x) + 1)) mod 8) with pad; rewrite SL, Z2Nat.id by lia; lia|].
  split; [rewrite length_app; cbn [length]; rewrite SL; destruct DJ as [D|D]; [left; lia | right; exact D]|].
  split; [exact HOMEc|].
  intros a Ha. apply NRA. rewrite length_app in Ha. cbn [length] in Ha. rewrite SL in Ha. lia.
Qed.


Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RFREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.

Lemma shapes_kept : forall K L A regs mem md E excl L' A' regs' mem' md',
  call_pre_k B (aa_MR API) K L A regs mem md ->
  call_post_rec B (aa_MR API) K L A regs mem md E excl L' A' regs' mem' md' ->
  (forall a, rec_shape_of_c.G_SHAPES <= a < rec_shape_of_c.G_SHAPES + 448 -> ~ E a) ->
  bytes_at rsegs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
  bytes_at rsegs mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes.
Proof using SEGS RIMG RFREE.
  intros K L A regs mem md E excl L' A' regs' mem' md' PRE POST HE BS.
  pose proof alloc_ceiling_val as AC.
  destruct PRE as (HM & _ & _ & _ & _ & HCE & _).
  destruct POST as (PM & _ & _ & _ & _ & _ & _ & PF & _).
  assert (GL : length rec_shape_of_c.g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  assert (RL : in_globals frame_RELRO (rec_shape_of_c.G_SHAPES + i)).
  { exists 0x224a8, 1472. split; [left; reflexivity | unfold rec_shape_of_c.G_SHAPES; lia]. }
  destruct (RIMG _ RL) as (I1 & _ & _ & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  rewrite <- SEGS.
  assert (NS : ~ scratch_k B K regs (rec_shape_of_c.G_SHAPES + i))
    by (unfold scratch_k; intros [H|H]; [lia | exact (I4 H)]).
  exact (proj1 (PF _ (or_intror I1) (RFREE _ _ _ _ _ HM RL) (RFREE _ _ _ _ _ PM RL) NS
                 (HE (rec_shape_of_c.G_SHAPES + i) ltac:(lia)))).
Qed.

Lemma rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  bytes_at rsegs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
  bytes_at rsegs mc rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes.
Proof using SEGS RIMG.
  intros K S O L A mem md Lc Ac mc mdc RJ BS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  assert (GL : length rec_shape_of_c.g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  assert (RL : in_globals frame_RELRO (rec_shape_of_c.G_SHAPES + i)).
  { exists 0x224a8, 1472. split; [left; reflexivity | unfold rec_shape_of_c.G_SHAPES; lia]. }
  destruct (RIMG _ RL) as (I1 & I2 & I3 & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  assert (NS : ~ (S - K <= rec_shape_of_c.G_SHAPES + i < S)) by lia.
  assert (NR : ~ rec_area (rec_shape_of_c.G_SHAPES + i))
    by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, rec_shape_of_c.G_SHAPES; lia).
  rewrite <- SEGS. exact (proj1 (HF _ (or_intror (conj I1 (conj I2 I3))) NS I4 NR)).
Qed.
End Stub.

Lemma fpk_trans : forall f1 f2 f3 : YK11.FPState, fp_kept f1 f2 -> fp_kept f2 f3 -> fp_kept f1 f3.
Proof. intros f1 f2 f3 (_ & H1) (C & H2). split; [exact C|]. intros r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma getr_nz : forall r, callee_saved r -> bv_eqb (Z_to_bv 5 r) 0 = false.
Proof.
  intros r Hr. assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.

Lemma pres_mid : forall regs R1 R2 R3 M1 M3,
  Regs6ss.xregs_eqv M1 R1 -> regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 ->
     reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r) /\ reg_get M1 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
  intros regs R1 R2 R3 M1 M3 X1 P X3 K r Hr N2 N8 N9.
  pose proof (getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (K r Hr N2 N8 N9) as [E1 E2]. rewrite E1, <- E2.
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3. symmetry. apply X1. exact NZ.
Qed.

Lemma pres_tail : forall regs R1 R2 R3 M3,
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> r = 2 \/ r = 8 \/ r = 9 -> reg_get M3 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R3.
Proof.
  intros regs R1 R2 R3 M3 P1 P X3 K1 K2 r Hr.
  pose proof (getr_nz r Hr) as NZ.
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (Z.eq_dec r 2) as [E|N2]; [exact (K2 r Hr (or_introl E))|].
  destruct (Z.eq_dec r 8) as [E|N8]; [exact (K2 r Hr (or_intror (or_introl E)))|].
  destruct (Z.eq_dec r 9) as [E|N9]; [exact (K2 r Hr (or_intror (or_intror E)))|].
  rewrite (K1 r Hr N2 N8 N9).
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3.
  pose proof (P1 r Hr N2 N8 N9) as E4. unfold getr in E4. rewrite NZ in E4. exact E4.
Qed.
