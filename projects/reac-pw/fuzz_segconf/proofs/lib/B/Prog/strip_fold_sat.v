(* reac-pw/fuzz_segconf, ASan+UBSan image B: the satisfiability check (stream rule T0.6, "a contract text gets a
   witness before provers use it") of the two contract texts lib/B/Prog/strip_c.v and lib/B/Prog/fold_c.v.

   proves no function (kind: statement text; closed satisfiability lemmas of contract premises). Every lemma here is
   closed: Print Assumptions lists only the Rocq primitives and functional extensionality.

   The form is the segconf porter's lib/U/Prog/sat/F234Sat.v (one closed lemma per premise set, at a real call site with real
   values), moved to the ASan reader: a premise here is stated over (ly, S, W, mem, regs), so the witness is a concrete
   layout LY, allocator state ST, world WS (no materialised-hole map: w_H = false everywhere), memory MEM (every byte
   present: the text block's bytes, the two strip cells, and 0 elsewhere, so every shadow byte reads 0) and register
   file. Every lemma holds for EVERY image segment list segs and EVERY asyms B (both are section variables), so it
   holds at image B's own segs and B.

   THE INSTANCE: m_file's turn on a text block t holding the line "  role = Box ;c\n" and its NUL (17 bytes: a malloc
   chunk of the primary allocator, its user bytes at TX = ly_space + 0x300000000 + 16), m_file's s1 = SP_MF, its
   class-1 side-stack frame (1, 0) at FB with low = FB + 32.
   - strip, m_file 0x864c0 (c:285): a0 = s1 + 176 holding TX (the line start), a1 = s1 + 168 holding TX + 13 (the
     comment mark ';'), l = the 13 bytes "  role = Box ". The post: strip_lead = 2, strip_trail = 1, the cells end at
     TX + 2 and TX + 12, and the bytes between them are h_strip l = "role = Box" (strip_mid).
   - fold, m_file 0x86738 (c:219, the role): a0 = v = TX + 9 ("Box" after the key "role" and '='), a1 = vn = 3, a2 =
     low, a3 = 64. The post: fold_out l 64 = "box", a0 = 3.

   WHAT IS NOT WITNESSED HERE, and why: afn_pre (the whole allocator relation AR, the run ceiling, the frame chain)
   and st_nev's bound against a REAL allocator state: a state satisfying AR is the harness walk's (the image-A owner's
   T0.6 note: "owed by the walk of the caller"; for m_file's callees, m_file's B walk). ST below is a hand-built
   astate with the one text chunk and the one frame, not a state reached by the allocator; LY, WS and MEM are chosen
   to meet the premises, not computed by a run. Every premise of strip_pre / fold_pre and every register premise is
   witnessed; together with the contracts' `st_nev S + EV <= EV_MAX` at ST. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import strip_c fold_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== the numbers ======================================== *)
(* the text "  role = Box ;c\n" and its NUL *)
Definition TXT : list Z := [32; 32; 114; 111; 108; 101; 32; 61; 32; 66; 111; 120; 32; 59; 99; 10; 0].
Definition LY_SPACE : Z := 0x600000000000.
Definition TXOFF : Z := 0x300000000.
(* the user bytes of the text chunk: ly_space + TXOFF + rz_size 17 *)
Definition TX : Z := 0x600300000010.
Definition LY_F : Z := 0x7fff70000000.
(* frame_addr LY 1 0 = LY_F + fs_frame_off 1 0 *)
Definition FB : Z := 0x7fff70109000.
Definition LOW : Z := 0x7fff70109020.
Definition LY_TOP : Z := 0x7ffffffff000.
(* m_file's s1, 32-aligned; the two strip cells of the site 0x864c0 *)
Definition SP_MF : Z := 0x7fffffffd000.
Definition SC : Z := 0x7fffffffd0b0.
Definition EC : Z := 0x7fffffffd0a8.

Lemma SC_is : SC = SP_MF + 176. Proof. reflexivity. Qed.
Lemma EC_is : EC = SP_MF + 168. Proof. reflexivity. Qed.
Lemma LOW_is : LOW = FB + 32. Proof. reflexivity. Qed.

(* the 13 bytes of the line after the comment cut, and the 3 bytes of the value *)
Definition LINE : list byte := seg_spec.zb (firstn 13 TXT).
Definition BOX : list byte := seg_spec.zb [66; 111; 120].

(* ======================================== the state ======================================== *)
Definition LY : alayout :=
  YG0f.ALayout 0 LY_SPACE 0 0 0 LY_F 0 0 LY_TOP (LY_TOP - 0x800000) LY_TOP 0 [] [] 0 [] (0, 0) (fun _ => 0).
Definition TCHUNK : YG00.chunk := YG00.mkChunk (YG00.PPrim TXOFF) 17 YG00.CAllocated.
Definition ST : YG00.astate :=
  YG00.mkA (repeat YG00.region0 32) false (repeat YG00.pclass0 32) [TCHUNK] [] [] 0 YG00.qc0 YG00.qc0
    (YG00.mkFS (repeat 0 11) [(1, 0)]) [] false 0.

Lemma hoff0 : forall segs, H_off_segments segs (fun _ => false).
Proof. intros segs a H. cbv beta in H. discriminate H. Qed.
Lemma awf0 : A_wf [].
Proof. constructor. Qed.
Definition WS (segs : list Segment) : world segs :=
  {| w_H := fun _ => false; w_A := []; w_Hoff := hoff0 segs; w_Awf := awf0; w_H8 := fun _ _ => eq_refl |}.

(* every byte present: the text, the two cells, else 0 *)
Definition fz (a : Z) : Z :=
  if (TX <=? a) && (a <? TX + 17) then nth (Z.to_nat (a - TX)) TXT 0
  else if (SC <=? a) && (a <? SC + 8) then le_byte TX 8 (Z.to_nat (a - SC))
  else if (EC <=? a) && (a <? EC + 8) then le_byte (TX + 13) 8 (Z.to_nat (a - EC))
  else 0.
Definition MEM : word -> option byte := fun w => Some (Z_to_bv 8 (fz (bv_unsigned w))).

Definition REGS_STRIP : bvmap 5 word :=
  regupd (regupd (regupd bvmap_empty (Z_to_bv 5 2) (Z_to_bv 64 SP_MF)) (Z_to_bv 5 10) (Z_to_bv 64 SC))
    (Z_to_bv 5 11) (Z_to_bv 64 EC).
Definition REGS_FOLD : bvmap 5 word :=
  regupd (regupd (regupd (regupd (regupd bvmap_empty (Z_to_bv 5 2) (Z_to_bv 64 SP_MF))
    (Z_to_bv 5 10) (Z_to_bv 64 (TX + 9))) (Z_to_bv 5 11) (Z_to_bv 64 3)) (Z_to_bv 5 12) (Z_to_bv 64 LOW))
    (Z_to_bv 5 13) (Z_to_bv 64 64).

(* ======================================== layout facts ======================================== *)
Lemma frame_LY : frame_addr LY 1 0 = FB.
Proof. vm_compute. reflexivity. Qed.
Lemma fsb1 : fs_frame_bytes 1 = 128.
Proof. vm_compute. reflexivity. Qed.
Lemma ablocks_ST : forall B, ablocks B LY ST = [(TX, 17)].
Proof. intros B. vm_compute. reflexivity. Qed.
Lemma frames_ST : frames ST = [(1, 0)].
Proof. reflexivity. Qed.
Lemma spZ_strip : spZ REGS_STRIP = SP_MF.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the reader ======================================== *)
Lemma fz_range : forall a, 0 <= fz a < 256.
Proof.
  intros a. unfold fz.
  destruct ((TX <=? a) && (a <? TX + 17)).
  - remember (Z.to_nat (a - TX)) as n eqn:En. clear En.
    do 18 (destruct n as [|n]; [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity|]).
    split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
  - destruct ((SC <=? a) && (a <? SC + 8)); [unfold le_byte; apply Z.mod_pos_bound; lia|].
    destruct ((EC <=? a) && (a <? EC + 8)); [unfold le_byte; apply Z.mod_pos_bound; lia | lia].
Qed.

Lemma fz_out : forall a, ~ (TX <= a < TX + 17) -> ~ (SC <= a < SC + 8) -> ~ (EC <= a < EC + 8) -> fz a = 0.
Proof.
  intros a H1 H2 H3. unfold fz.
  destruct ((TX <=? a) && (a <? TX + 17)) eqn:E1.
  { apply andb_true_iff in E1 as [E1 E1']. apply Z.leb_le in E1. apply Z.ltb_lt in E1'. lia. }
  destruct ((SC <=? a) && (a <? SC + 8)) eqn:E2.
  { apply andb_true_iff in E2 as [E2 E2']. apply Z.leb_le in E2. apply Z.ltb_lt in E2'. lia. }
  destruct ((EC <=? a) && (a <? EC + 8)) eqn:E3.
  { apply andb_true_iff in E3 as [E3 E3']. apply Z.leb_le in E3. apply Z.ltb_lt in E3'. lia. }
  reflexivity.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

Lemma RD_at : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H (WS segs)) MEM a = Some (fz a).
Proof.
  intros a Ha. unfold aview, mbyte, mrestrict. cbn [WS w_H MEM option_map].
  rewrite !Z_to_bv_unsigned.
  assert (E64 : bv_wrap 64 a = a).
  { unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  rewrite E64. pose proof (fz_range a) as R.
  assert (E8 : bv_wrap 8 (fz a) = fz a).
  { unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8). apply Z.mod_small. lia. }
  rewrite E8. reflexivity.
Qed.

Lemma RD_some : forall a, aview segs (w_H (WS segs)) MEM a <> None.
Proof. intros a. unfold aview, mbyte, mrestrict. cbn [WS w_H MEM option_map]. discriminate. Qed.

Lemma pres_W : forall a, apresent (w_H (WS segs)) MEM a.
Proof. intros a. split; [reflexivity | eexists; reflexivity]. Qed.

(* [q, q + n) addressable when no shadow byte of it falls on the text or a cell *)
Lemma ra_W : forall q n, 0 <= q -> q + n <= 2 ^ 63 ->
  (forall x, q <= x < q + n -> fz (shadow_of_addr SHADOW_OFF x) = 0) ->
  range_addressable (aview segs (w_H (WS segs)) MEM) SHADOW_OFF q n.
Proof.
  intros q n H0 H1 H3 x Hx. exists 0. split; [|left; reflexivity].
  rewrite RD_at; [rewrite (H3 x Hx); reflexivity|].
  clear H3. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Lemma sa_addr_W : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> amem_range q n ->
  (forall x, q <= x < q + n -> fz (shadow_of_addr SHADOW_OFF x) = 0) ->
  sa_addr (aview segs (w_H (WS segs)) MEM) q n.
Proof.
  intros q n H0 H1 H2 H3. unfold sa_addr.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact (ra_W q n H0 H1 H3)|].
  intros _ s _. apply RD_some.
Qed.

Ltac amem := unfold amem_range; right; split; apply Z.leb_le; vm_compute; reflexivity.
Ltac shadow_out :=
  intros x Hx; apply fz_out; unfold shadow_of_addr, SHADOW_OFF, TX, SC, EC, LOW in *;
  Z.div_mod_to_equations; lia.

Lemma sa_addr_SC : sa_addr (aview segs (w_H (WS segs)) MEM) SC 8.
Proof. apply sa_addr_W; [unfold SC; lia | unfold SC; lia | amem | shadow_out]. Qed.
Lemma sa_addr_EC : sa_addr (aview segs (w_H (WS segs)) MEM) EC 8.
Proof. apply sa_addr_W; [unfold EC; lia | unfold EC; lia | amem | shadow_out]. Qed.
Lemma sa_addr_LINE : sa_addr (aview segs (w_H (WS segs)) MEM) TX (TX + 13 - TX).
Proof. apply sa_addr_W; [unfold TX; lia | unfold TX; lia | amem | shadow_out]. Qed.
Lemma sa_addr_BOX : sa_addr (aview segs (w_H (WS segs)) MEM) (TX + 9) 3.
Proof. apply sa_addr_W; [unfold TX; lia | unfold TX; lia | amem | shadow_out]. Qed.
Lemma ra_LOW : range_addressable (aview segs (w_H (WS segs)) MEM) SHADOW_OFF LOW (3 + 1).
Proof. apply ra_W; [unfold LOW; lia | unfold LOW; lia | shadow_out]. Qed.

(* Every lemma below is proved directly; no proof tries a lemma whose numbers differ from the goal's (a failing
   `exact` between two stuck terms with different literals makes the unifier compare them branch by branch). *)
Lemma sa_val_SC : sa_val (aview segs (w_H (WS segs)) MEM) SC 8%nat TX.
Proof.
  intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.
Lemma sa_val_EC : sa_val (aview segs (w_H (WS segs)) MEM) EC 8%nat (TX + 13).
Proof.
  intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.
Lemma LINE_length : length LINE = 13%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma sa_bytes_LINE : sa_bytes (aview segs (w_H (WS segs)) MEM) TX LINE.
Proof.
  intros i Hi. rewrite LINE_length in Hi.
  do 13 (destruct i as [|i]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.

Lemma fold_out_BOX : fold_out BOX 64 = [98; 111; 120].
Proof. vm_compute. reflexivity. Qed.
Lemma fold_out_BOX_len : Z.of_nat (length (fold_out BOX 64)) = 3.
Proof. rewrite fold_out_BOX. reflexivity. Qed.
Lemma fold_out_BOX_nat : length (fold_out BOX 64) = 3%nat.
Proof. rewrite fold_out_BOX. reflexivity. Qed.
Lemma BOX3_length : length (firstn 3 BOX) = 3%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma sa_bytes_BOX : sa_bytes (aview segs (w_H (WS segs)) MEM) (TX + 9) (firstn 3 BOX).
Proof.
  intros i Hi. rewrite BOX3_length in Hi.
  do 3 (destruct i as [|i]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.

Lemma heap_TX : forall q n, TX <= q -> q + n <= TX + 17 -> sa_heap B LY ST q n.
Proof. intros q n H1 H2. exists TX, 17. rewrite ablocks_ST. split; [left; reflexivity | lia]. Qed.

(* ===================================== strip: the premises ===================================== *)
Lemma SC_mod8 : SC mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma EC_mod8 : EC mod 8 = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma disj_cells : sa_disj SC 8 EC 8.
Proof. unfold sa_disj, SC, EC. lia. Qed.
Lemma TX_bounds : 0 < TX <= TX + 13.
Proof. unfold TX. lia. Qed.
Lemma LINE_len : Z.of_nat (length LINE) = TX + 13 - TX.
Proof. rewrite LINE_length. lia. Qed.
Lemma disj_LINE_SC : sa_disj TX (TX + 13 - TX) SC 8.
Proof. unfold sa_disj, TX, SC. lia. Qed.
Lemma disj_LINE_EC : sa_disj TX (TX + 13 - TX) EC 8.
Proof. unfold sa_disj, TX, EC. lia. Qed.
Lemma strip_slot_SC : strip_slot LY (w_H (WS segs)) MEM (spZ REGS_STRIP) SC.
Proof.
  split; [rewrite spZ_strip; unfold SC, SP_MF; lia|].
  split; [change (ly_top LY) with LY_TOP; unfold SC, LY_TOP; lia | intros i _; apply pres_W].
Qed.
Lemma strip_slot_EC : strip_slot LY (w_H (WS segs)) MEM (spZ REGS_STRIP) EC.
Proof.
  split; [rewrite spZ_strip; unfold EC, SP_MF; lia|].
  split; [change (ly_top LY) with LY_TOP; unfold EC, LY_TOP; lia | intros i _; apply pres_W].
Qed.
Lemma loc_LINE : sa_loc segs B LY ST TX (TX + 13 - TX).
Proof. left. apply heap_TX; unfold TX; lia. Qed.

Lemma strip_args_sat : strip_args (aview segs (w_H (WS segs)) MEM) SC EC TX (TX + 13) LINE.
Proof.
  exact (conj SC_mod8 (conj EC_mod8 (conj disj_cells (conj sa_val_SC (conj sa_addr_SC (conj sa_val_EC
    (conj sa_addr_EC (conj TX_bounds (conj sa_bytes_LINE (conj LINE_len (conj sa_addr_LINE
    (conj disj_LINE_SC disj_LINE_EC)))))))))))).
Qed.

(* m_file 0x864c0: strip(s1 + 176, s1 + 168) on the line "  role = Box " of the text block *)
Lemma strip_pre_sat : strip_pre segs B LY ST (WS segs) MEM REGS_STRIP SC EC TX (TX + 13) LINE.
Proof. exact (conj strip_args_sat (conj strip_slot_SC (conj strip_slot_EC loc_LINE))). Qed.

(* the register premises and the event bound of strip_contract at the same instance *)
Lemma getr_strip10 : getr REGS_STRIP 10 = w64 SC.
Proof. vm_compute. reflexivity. Qed.
Lemma getr_strip11 : getr REGS_STRIP 11 = w64 EC.
Proof. vm_compute. reflexivity. Qed.
Lemma ev_ST : st_nev ST + 0 <= EV_MAX.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma strip_regs_sat :
  getr REGS_STRIP 10 = w64 SC /\ 0 <= SC < 2 ^ 64 /\ getr REGS_STRIP 11 = w64 EC /\ 0 <= EC < 2 ^ 64 /\
  st_nev ST + EV_strip <= EV_MAX.
Proof.
  split; [exact getr_strip10|]. split; [unfold SC; lia|]. split; [exact getr_strip11|].
  split; [unfold EC; lia|]. exact ev_ST.
Qed.

(* ===================================== fold: the premises ===================================== *)
Lemma frame_LOW : sa_fframe LY ST LOW (3 + 1).
Proof.
  exists 1, 0. rewrite frames_ST, frame_LY, fsb1.
  split; [left; reflexivity|]. unfold FB, LOW. lia.
Qed.
Lemma fold_s_nz : 0 < Z.of_nat (length (fold_out BOX 64)) -> TX + 9 <> 0.
Proof. intros _. unfold TX. lia. Qed.
Lemma sa_bytes_BOXK : sa_bytes (aview segs (w_H (WS segs)) MEM) (TX + 9) (firstn (length (fold_out BOX 64)) BOX).
Proof. rewrite fold_out_BOX_nat. exact sa_bytes_BOX. Qed.
Lemma sa_addr_BOXK : sa_addr (aview segs (w_H (WS segs)) MEM) (TX + 9) (Z.of_nat (length (fold_out BOX 64))).
Proof. rewrite fold_out_BOX_len. exact sa_addr_BOX. Qed.
Lemma ra_LOWK :
  range_addressable (aview segs (w_H (WS segs)) MEM) SHADOW_OFF LOW (Z.of_nat (length (fold_out BOX 64)) + 1).
Proof. rewrite fold_out_BOX_len. exact ra_LOW. Qed.
Lemma disj_BOX_LOW : sa_disj (TX + 9) (Z.of_nat (length (fold_out BOX 64))) LOW (Z.of_nat (length (fold_out BOX 64)) + 1).
Proof. rewrite fold_out_BOX_len. unfold sa_disj, TX, LOW. lia. Qed.
Lemma BOX_len : Z.of_nat (length BOX) = 3.
Proof. vm_compute. reflexivity. Qed.
Lemma cap_ok : 1 <= 64.
Proof. lia. Qed.
Lemma loc_BOXK : sa_loc segs B LY ST (TX + 9) (Z.of_nat (length (fold_out BOX 64))).
Proof. rewrite fold_out_BOX_len. left. apply heap_TX; unfold TX; lia. Qed.
Lemma frame_LOWK : sa_fframe LY ST LOW (Z.of_nat (length (fold_out BOX 64)) + 1).
Proof. rewrite fold_out_BOX_len. exact frame_LOW. Qed.

Lemma fold_args_sat : fold_args (aview segs (w_H (WS segs)) MEM) (TX + 9) 3 LOW 64 BOX.
Proof.
  exact (conj cap_ok (conj BOX_len (conj fold_s_nz (conj sa_bytes_BOXK (conj sa_addr_BOXK
    (conj ra_LOWK disj_BOX_LOW)))))).
Qed.

(* m_file 0x86738: fold(v = TX + 9, 3, low, 64) on the role value "Box" *)
Lemma fold_pre_sat : fold_pre segs B LY ST (WS segs) MEM (TX + 9) 3 LOW 64 BOX.
Proof. exact (conj fold_args_sat (conj loc_BOXK frame_LOWK)). Qed.

Lemma getr_fold10 : getr REGS_FOLD 10 = w64 (TX + 9).
Proof. vm_compute. reflexivity. Qed.
Lemma getr_fold11 : getr REGS_FOLD 11 = w64 3.
Proof. vm_compute. reflexivity. Qed.
Lemma getr_fold12 : getr REGS_FOLD 12 = w64 LOW.
Proof. vm_compute. reflexivity. Qed.
Lemma getr_fold13 : getr REGS_FOLD 13 = w64 64.
Proof. vm_compute. reflexivity. Qed.
Lemma fold_regs_sat :
  getr REGS_FOLD 10 = w64 (TX + 9) /\ 0 <= TX + 9 < 2 ^ 64 /\ getr REGS_FOLD 11 = w64 3 /\ 0 <= 3 < 2 ^ 64 /\
  getr REGS_FOLD 12 = w64 LOW /\ 0 <= LOW < 2 ^ 64 /\ getr REGS_FOLD 13 = w64 64 /\ 0 <= 64 < 2 ^ 64 /\
  st_nev ST + EV_fold <= EV_MAX.
Proof.
  split; [exact getr_fold10|]. split; [unfold TX; lia|]. split; [exact getr_fold11|]. split; [lia|].
  split; [exact getr_fold12|]. split; [unfold LOW; lia|]. split; [exact getr_fold13|]. split; [lia|].
  exact ev_ST.
Qed.
End w.

(* ===================================== the posts at the instance ===================================== *)
(* strip: 2 leading blanks, 1 trailing; the cells end at TX + 2 and TX + 12; the bytes between are h_strip l =
   "role = Box" (strip_c.strip_mid at this l). *)
Lemma strip_post_sat :
  strip_lead (seg_spec.zs LINE) = 2%nat /\ strip_trail (seg_spec.zs LINE) = 1%nat /\
  TX + Z.of_nat (strip_lead (seg_spec.zs LINE)) = TX + 2 /\
  TX + 13 - Z.of_nat (strip_trail (seg_spec.zs LINE)) = TX + 12 /\
  h_strip (seg_spec.zs LINE) = [114; 111; 108; 101; 32; 61; 32; 66; 111; 120] /\
  firstn (13 - 2 - 1) (skipn 2 (seg_spec.zs LINE)) = h_strip (seg_spec.zs LINE).
Proof.
  assert (L : strip_lead (seg_spec.zs LINE) = 2%nat) by (vm_compute; reflexivity).
  assert (T : strip_trail (seg_spec.zs LINE) = 1%nat) by (vm_compute; reflexivity).
  rewrite L, T. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; vm_compute; reflexivity.
Qed.

(* fold: k = 3 = min(3, 64 - 1), out holds "box" and the NUL. *)
Lemma fold_post_sat :
  fold_out BOX 64 = [98; 111; 120] /\ Z.of_nat (length (fold_out BOX 64)) = Z.min 3 (64 - 1) /\
  seg_spec.zb (fold_out BOX 64 ++ [0]) = seg_spec.zb [98; 111; 120; 0].
Proof.
  split; [exact fold_out_BOX|]. split; [rewrite fold_out_BOX_len; reflexivity|].
  rewrite fold_out_BOX. reflexivity.
Qed.
