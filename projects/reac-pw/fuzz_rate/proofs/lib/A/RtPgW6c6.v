(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the block lemma w6c_h6 of
   lib/A/RtPgW6cBase.v, the head of case 6 of ent_build's `switch (kind % 10)` (pod.h:340-348) inside
   LLVMFuzzerTestOneInput (0x80714), from the case entry 0x81880 to the entry of __asan_memcpy 0x51860.
   Proves no function (kind: segment lemma).

   THE CODE (registers as in RtPgW6cBase.v: s1 = R, s2 = SHADOW_OFF, s9 = c, s8 = |r|, a4 = c - 1, a5 = |r| + 1):
     0x81880  beqz s8 -> 0x81b24                      no byte left
     0x81884 .. 0x81894  the check of s9 (NE-SLOW, slow block 0x821b8), `ld s6,0xe8(s1)` inside
     0x81898  lbu a2,0(s9) (= t); a2 := t & 3; a0 := 0x211c0 + 4 (t & 3)
     0x818b0 .. 0x818bc  the check of a0, 4 bytes (NE-SLOW, slow block 0x821c4)
     0x818c0  beq a2,2 -> 0x81c90 (a3 := 4); else a3 := 8
     0x81c94  a1 := a5 - 2 (= |r1|); s9 := a4 + 2; lw a0,0(a0) (the type); a2 := (t & 3 = 3) ? 0 : a3 (the size)
     0x81b24  (no byte) a1 := 0; a2 := 8; a0 := 5; s6 := [R+0xe8]; j 0x81cb0
     0x81cb0  a3 := [R+0x138] (= &e); e.type := a0; e.size := a2; bltu a2,a1 -> 0x81cc4; else a2 := a1
     0x81cc4  a3 := s9 + a2; s8 := a1 - a2; a0 := [R+0x108] (= &e.body); a1 := s9; s9 := a3
     0x81cd8  jal __asan_memcpy (0x51860), ra = 0x81cdc
   THE PROOF. The engine state at the entry holds the registers as their own atoms and three extra atoms: 32 = vb,
   33 = F, 34 = t (the input byte, 0 when none is left). The cells [R+0xe8, R+0x110) (vb, &e.body) and
   [R+0x138, R+0x140) (&e) are regions based at s1 without a write window.
     no byte left: s8 pinned to 0; e's header [F+0xf0, F+0xf8) a region based at atom 33 with that write window
       (in the side-stack frame (3, pos)); one run (lib/Reusable/YCbq.v aj_run_to) to 0x51860.
     a byte t: the byte a one-byte region based at s9; one run of the token engine (YCbq aj_run_to_tok over
       lib/Reusable/YCbn.v) to 0x818c0, which leaves the two checks' obligations (the input's range_addressable and
       the table's); then t & 3 = j is split (four cases), a2 and a0 pinned to the literals j and 0x211c0 + 4 j,
       the input region dropped and e's header region and the table (16 bytes of .rodata) added (h6_reseat; the
       table lies in the image, the frame does not: AR_client_img_law); one run to the `bltu` 0x81cbc, the branch
       split (srr_branch_sh), one run to 0x51860.
   At 0x51860 the registers are read from the final symbolic state, e.type and e.size from the chunks of e's region,
   and every byte outside e's header is kept by the runs' frames. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSteps RtPgSeg RtPgW6cBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image A's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the engine states ======================================== *)
Definition H6_CK : Z := 0x818c0.   (* past the table's check: `addi a1,zero,2; beq a2,a1` *)
(* the real frame's cells: [R+0xe8] = vb (atom 32), [R+0x108] = F + 0xf8, [R+0x138] = F + 0xf0 (atom 33 = F) *)
Definition h6_rC1 : YP09.region := YP09.mkRegion (Some 9%nat) 0xe8 0x110 0 0
  [YP09.mkChunk 0xe8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x108 (CVal 8 (SOff 33 0xf8))].
Definition h6_rC2 : YP09.region := YP09.mkRegion (Some 9%nat) 0x138 0x140 0 0
  [YP09.mkChunk 0x138 (CVal 8 (SOff 33 0xf0))].
(* the input byte t at s9 (atom 34) *)
Definition h6_rI : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
(* e's header, written *)
Definition h6_rE : YP09.region := YP09.mkRegion (Some 33%nat) 0xf0 0xf8 0xf0 0xf8 [].
(* case 6's t[] in .rodata *)
Definition h6_rT : YP09.region := YP09.mkRegion None W6C_T6 (W6C_T6 + 16) 0 0 [YP09.mkChunk W6C_T6 (CImg 16)].
(* the token engine's facts: s2 = SHADOW_OFF, s8 = |r| >= 1, s9 = c, t a byte *)
Definition h6_G1 : facts := mkFacts [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, mkAF 1 (2 ^ 47) 0);
  (25%nat, mkAF 2 (2 ^ 47 - 2) 0); (34%nat, mkAF 0 255 0)] [] [].
Definition h6_Bx : sv := SOff 18 0.
Definition h6_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition h6_extra (vb F t : Z) : list word := [w64 vb; w64 F; w64 t].
Definition h6_ss0 : sstate := mkSS W6C_D6 sr_atoms [h6_rE; h6_rC1; h6_rC2] None (mkFacts [] [] []).
Definition h6_ss1 : sstate := mkSS W6C_D6 sr_atoms [h6_rC1; h6_rC2; h6_rI] None h6_G1.
(* at 0x818c0, after the split t & 3 = j *)
Definition h6_ss2 (ss : sstate) (j : Z) : sstate :=
  mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) (12%bv : bv 5) (SLit j)) (10%bv : bv 5) (SLit (W6C_T6 + 4 * j)))
    [h6_rE; h6_rT; h6_rC1; h6_rC2] None (ss_facts ss).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ======================================== arithmetic ======================================== *)
Lemma h6_U_and3 : forall E v, ew E 34 = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SOff 34 0) (SLit 3)) = v mod 4.
Proof.
intros E v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E 34 v H) by lia.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity.
Qed.
(* a0 after `add a0,a0,a1` at 0x818ac, as the engine holds it *)
Lemma h6_U_tbl : forall E v, ew E 34 = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_ADD (SLit 135616) (SAlu ALU_SLL (SAlu ALU_AND (SOff 34 0) (SLit 3)) (SLit 2))) =
  W6C_T6 + 4 * (v mod 4).
Proof.
intros E v H Hv. pose proof (Z.mod_pos_bound v 4 ltac:(lia)) as Hm.
rewrite U_SAlu, U_SLit, U_SAlu, (h6_U_and3 E v H Hv), U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (v mod 4 * 4)) by (unfold M64; lia).
rewrite (zcanon_id 135616) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). unfold W6C_T6. lia.
Qed.
(* a register's symbolic value at a leaf, as a value *)
Lemma h6_den_lit : forall E z v, z = v -> sv_denot E (SLit z) = w64 v.
Proof. intros E z v ->. reflexivity. Qed.
Lemma h6_den_off : forall E n a k v, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> 0 <= a + k < 2 ^ 64 -> v = a + k ->
  sv_denot E (SOff n k) = w64 v.
Proof. intros E n a k v H Ha Hak ->. rewrite denot_lit_U, (U_atom_off E n a k H Ha Hak). reflexivity. Qed.
Lemma h6_den_add : forall E n m a b v, ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b -> 0 <= a -> 0 <= b ->
  a + b < 2 ^ 64 -> v = a + b -> sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = w64 v.
Proof.
intros E n m a b v Hn Hm Ha Hb Hab ->. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n a Hn) by lia. rewrite (U_atom E m b Hm) by lia. rewrite zcanon_id by (unfold M64; lia).
reflexivity.
Qed.
Lemma h6_af : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi H Hv Hb. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. split; [lia | split; [reflexivity | lia]].
Qed.

(* ======================================== the engine state's pieces ======================================== *)
(* the same machine state seen through other registers and regions (the facts kept) *)
Lemma h6_reseat : forall E ss ms rg rs, st_ok rsegs E ss ms -> ss_resv ss = None ->
  regs_ok E rg (ms_regs ms) -> mem_ok rsegs E (ms_mem ms) rs ->
  st_ok rsegs E (mkSS (ss_pc ss) rg rs None (ss_facts ss)) ms.
Proof.
intros E ss ms rg rs (H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & H9) Hrv Hr Hm.
rewrite Hrv in H4. unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact Hr|]. split; [exact Hm | exact H9].
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma h6_keep0 : forall E rs (H : word -> bool) (m1 m2 : word -> option byte),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 HF Hro a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
(* a literal chunk of region i of a run's state, at absolute address a *)
Lemma h6_val_at : forall E ss (H : word -> bool) ms i r off (n : N) z b a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n (SLit z))) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
  0 <= z < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> a = b + off ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) z.
Proof.
intros E ss H ms i r off n z b a HS Hi Hc Hb Hz Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (val_of_chunk_ok rsegs E _ b off n (SLit z) z Hck eq_refl Hz Hn).
Qed.

(* ======================================== the table and the frame ======================================== *)
Lemma h6_tbl_img : forall a, W6C_T6 <= a < W6C_T6 + 16 -> in_img rsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun sg : Segment => (Z.of_N (seg_base sg) <=? W6C_T6) &&
  (W6C_T6 + 16 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.
(* e's header (in a frame for locals, outside the image) and the table (in the image) are apart *)
Lemma h6_e_tbl : forall B ly S W mem md pos, AR_laws rsegs B -> AR rsegs B ly S W mem md -> In (3, pos) (frames S) ->
  frame_addr ly 3 pos + 0xf8 <= W6C_T6 \/ W6C_T6 + 16 <= frame_addr ly 3 pos + 0xf0.
Proof.
intros B ly S W mem md pos LAWS HAR Hin.
destruct (Z_le_gt_dec (frame_addr ly 3 pos + 0xf8) W6C_T6) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (W6C_T6 + 16) (frame_addr ly 3 pos + 0xf0)) as [H'|H']; [right; exact H'|].
exfalso.
pose proof (al_client_img _ _ LAWS ly S W mem md (Z.max (frame_addr ly 3 pos + 0xf0) W6C_T6) HAR) as Hc.
apply (proj2 (Hc ltac:(right; left; exists 3, pos; split; [exact Hin | change (fs_frame_bytes 3) with 512; lia]))).
apply h6_tbl_img. lia.
Qed.

Context {SK : YI16.sink_head}.

(* ======================================== tactics ======================================== *)
Ltac h6_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; h6_kio].
(* the write window of a run's first region (e's header, based at atom 33 = F = frame_addr lyc 3 pos) *)
Ltac h6_awr U33 HFa Hown pos :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  eapply (rts_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 33%nat pos 0);
  [ reflexivity | rewrite U33, Z.add_0_r; exact HFa | exact Hown | cbn; lia | cbn; lia | awr_ok_tac ].
(* after a run: every byte outside e's header kept since the segment's start *)
Ltac h6_ke F W U33 :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2),
    KE : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> aview _ _ ?m1 a = aview _ _ ?mc a |- _ =>
    let rs' := eval vm_compute in rs in
    let KE' := fresh "KE" in
    assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0xf8) ->
      aview rsegs (w_H W) m2 a = aview rsegs (w_H W) mc a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
      intros a Ha Hn; transitivity (aview rsegs (w_H W) m1 a); [|exact (KE a Ha Hn)];
      unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
      rewrite unsigned_lit_small by lia;
      let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Hra := fresh "Hra" in
      intros (rr & Hrr & Hra); change rs with rs' in Hrr; cbn [In] in Hrr;
      repeat (destruct Hrr as [Hrr | Hrr];
        [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; first [lia | rewrite U33 in Hra; lia] |]);
      destruct Hrr
    | clear KE HFr; rename KE' into KE ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* a register of the final state *)
Ltac h6_regv HS :=
  rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HS);
  match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
Ltac h6_reg HS :=
  h6_regv HS;
  first [ apply h6_den_lit; first [reflexivity | lia]
        | eapply h6_den_off; [eassumption | lia | lia | lia]
        | eapply h6_den_add; [eassumption | eassumption | lia | lia | lia | lia] ].
(* e.type / e.size from the chunk of e's region (the first region of the final state) *)
Ltac h6_val HS U33 off z :=
  lazymatch type of HS with st_ok _ ?Ex ?ssf (restrict ?H ?msf) =>
    let rr := eval vm_compute in (nth_error (ss_mem ssf) 0) in
    lazymatch rr with Some ?r0 =>
      eapply (h6_val_at Ex ssf H msf 0 r0 off 4%N z);
      [ exact HS | vm_compute; reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
      | cbn [YP09.r_base base_val]; exact U33 | cbn; lia | cbn; lia | lia ]
    end
  end.
(* the leaf at 0x51860: everything but Q *)
Ltac h6_leaf W HAE :=
  apply SRr_ret;
  lazymatch goal with
  | HS : st_ok _ ?Ex ?ssf (restrict _ ?msf), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memf ?mdf _,
    KE : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> aview _ _ ?memf a = _ |- _ =>
    unfold w6c_hpost; cbv beta;
    exists (ms_regs msf), (ms_mem msf), mdf;
    split; [reflexivity|];
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS eq_refl) at 1; reflexivity|];
    split; [exact HJ|];
    split; [h6_kio|];
    split; [eapply (RtPgSteps.regs_kept_of_st_ok rsegs _ _ msf _ _ (w_H W) _ HS HAE); vm_compute; reflexivity|];
    split; [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
            intros a Ha Hn; exact (KE a Ha Hn)|];
    cbv zeta; cbn [Cursor.fuzz_u8 fst snd]
  end.
(* the nine facts Q states *)
Ltac h6_q HS U33 TY SZ :=
  split; [h6_reg HS|]; split; [h6_reg HS|]; split; [h6_reg HS|]; split; [h6_reg HS|];
  split; [h6_reg HS|]; split; [h6_reg HS|]; split; [h6_reg HS|];
  split; [h6_val HS U33 240 TY | h6_val HS U33 244 SZ].
(* a branch condition on a5 - 2 = |r1| as a comparison *)
Ltac h6_hc E X15 Hc :=
  rewrite branch_ltu_U, U_SLit, (U_atom_off E 15 _ (-2) X15) in Hc by lia;
  rewrite zcanon_id in Hc by (unfold M64; lia);
  first [apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc].

(* ======================================== the block lemma ======================================== *)
Theorem w6c_h6 : forall B, w6c_h6_stmt B.
Proof.
intros B. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold w6c_h6_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb r
  (HJ & Hgeo & Hrom) Hregs Hcells Hin Hz Hra6.
destruct Hgeo as (HR16 & HRlo & HRhi & HRhm & Hown & HFa & HFapp & HF32).
destruct Hregs as (H2 & H3 & H4 & H9 & H18 & H25 & H24 & H14 & H15).
destruct Hcells as (V138 & V108 & Ve8 & Hvb & V10).
destruct Hin as (Hbytes & Hrain & Hhull & Hc1 & Hc63 & Hamr & Hdis).
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsl.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (HF4096 & HFceil & _).
rewrite <- HFa in HF4096, HFceil. change (fs_frame_bytes 3) with 512 in HFceil.
unfold T_SEG_STK, ASTACK in HRlo, HRhm, Hdis.
assert (BR : kHighMemBeg + 16384 <= R /\ R + 0x1e0 <= 2 ^ 47 /\ F + 512 + 16384 <= R) by lia.
clear Hceil Hslo Hshi H47 HFceil HRlo HRhi HRhm Hstk.
destruct BR as (BR1 & BR2 & BR3). unfold kHighMemBeg in BR1.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xf0 <= a < F + 0xf8) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 W6C_D6) with (Z_to_bv 64 W6C_D6).
destruct r as [|b r1].
- (* ======== no byte left: t = 0, size 8, n = 0 ======== *)
  cbn [length Z.of_nat] in H24.
  clear Hbytes Hrain Hhull Hdis Hamr.
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (_ & _ & Hfp & _).
  rewrite <- HFa in Hfp. change (fs_frame_bytes 3) with 512 in Hfp.
  remember (Ereg regs (h6_extra vb F 0)) as E0 eqn:HE0.
  assert (E9 : ew E0 9 = Z_to_bv 64 R) by (subst E0; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E25 : ew E0 25 = Z_to_bv 64 c) by (subst E0; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (E32 : ew E0 32 = Z_to_bv 64 vb) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E0 33 = Z_to_bv 64 F) by (subst E0; exact (ew_Ereg_extra regs _ 1)).
  assert (U9 : bv_unsigned (ew E0 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E0 33) = F) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs E0 h6_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D6) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E0. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + unfold h6_rE. apply (rtm_rw_region rsegs _ (w_H W) memc 33%nat F); [exact U33 | lia | lia | | constructor].
        intros o Ho. exact (proj1 (Hfp (F + o) ltac:(lia))).
      + unfold h6_rC1. apply (rtm_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val rsegs _ _ R 0xe8 8 (SOff 32 0) vb); [eapply h6_den_off; [exact E32 | lia | lia | lia]
            | cbn; lia | cbn; lia | exact Ve8].
        * apply (chunk_ok_val rsegs _ _ R 0x108 8 (SOff 33 0xf8) (F + 0xf8));
            [eapply h6_den_off; [exact E33 | lia | lia | lia] | cbn; lia | cbn; lia | exact V108].
      + unfold h6_rC2. apply (rtm_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 33 0xf0) (F + 0xf0));
          [eapply h6_den_off; [exact E33 | lia | lia | lia] | cbn; lia | cbn; lia | exact V138].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, h6_rE, h6_rC1, h6_rC2.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33. repeat split; lia.
    - split; [exact I | split; exact I]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (24%bv : bv 5) 0 HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; exact H24)) as HS1.
  clear HS. rename HS1 into HS.
  assert (HAE : env_agree 32 (Ereg regs (h6_extra vb F 0)) E0) by (subst E0; apply env_agree_refl).
  clear HE0.
  aj_run_to w6c_tbl_ok HS HJ W6C_CPY; [h6_awr U33 HFa Hown pos|].
  h6_ke F W U33.
  h6_leaf W HAE.
  cbn [length Z.of_nat].
  change (w6c_ty6 0) with 5. change (w6c_sz6 5) with 8.
  h6_q HS U33 5 8.
- (* ======== a byte t, the rest r1 ======== *)
  pose proof (Cursor.byte_range b) as Ht.
  assert (Hlen : Z.of_nat (length (b :: r1)) = Z.of_nat (length r1) + 1) by (cbn [length]; lia).
  pose proof (proj1 (rtm_bytes_aview rsegs (w_H W) memc c (b :: r1)) Hbytes 0%nat ltac:(cbn [length]; lia)) as Hb0.
  cbn [nth Z.of_nat] in Hb0. rewrite Z.add_0_r in Hb0.
  assert (Hcr : 2 <= c /\ c + Z.of_nat (length (b :: r1)) < 2 ^ 47).
  { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
  assert (Hdc : (c + 1 <= R + 0x60 \/ R + 0x120 <= c) /\ (c + 1 <= R + 0x128 \/ R + 0x140 <= c)).
  { destruct (Hdis c ltac:(lia)) as (_ & _ & D3 & D4 & _). lia. }
  clear Hdis Hamr Hhull Hc63.
  remember (Ereg regs (h6_extra vb F (bv_unsigned b))) as E1 eqn:HE1.
  assert (E9 : ew E1 9 = Z_to_bv 64 R) by (subst E1; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E14 : ew E1 14 = Z_to_bv 64 (c - 1)) by (subst E1; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
  assert (E15 : ew E1 15 = Z_to_bv 64 (Z.of_nat (length (b :: r1)) + 1))
    by (subst E1; rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
  assert (E18 : ew E1 18 = Z_to_bv 64 SHADOW_OFF) by (subst E1; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E24 : ew E1 24 = Z_to_bv 64 (Z.of_nat (length (b :: r1))))
    by (subst E1; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
  assert (E25 : ew E1 25 = Z_to_bv 64 c) by (subst E1; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (E32 : ew E1 32 = Z_to_bv 64 vb) by (subst E1; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E1 33 = Z_to_bv 64 F) by (subst E1; exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E1 34 = Z_to_bv 64 (bv_unsigned b)) by (subst E1; exact (ew_Ereg_extra regs _ 2)).
  assert (U9 : bv_unsigned (ew E1 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E1 25) = c) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs E1 h6_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D6) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E1. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + unfold h6_rC1. apply (rtm_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val rsegs _ _ R 0xe8 8 (SOff 32 0) vb); [eapply h6_den_off; [exact E32 | lia | lia | lia]
            | cbn; lia | cbn; lia | exact Ve8].
        * apply (chunk_ok_val rsegs _ _ R 0x108 8 (SOff 33 0xf8) (F + 0xf8));
            [eapply h6_den_off; [exact E33 | lia | lia | lia] | cbn; lia | cbn; lia | exact V108].
      + unfold h6_rC2. apply (rtm_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ R 0x138 8 (SOff 33 0xf0) (F + 0xf0));
          [eapply h6_den_off; [exact E33 | lia | lia | lia] | cbn; lia | cbn; lia | exact V138].
      + unfold h6_rI. apply (rtm_cell_region rsegs _ (w_H W) memc 25%nat c (bv_unsigned b) (SOff 34 0) U25 Hb0);
          [eapply h6_den_off; [exact E34 | lia | lia | lia] | lia | lia].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, h6_rC1, h6_rC2, h6_rI.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25. repeat split; lia.
    - unfold facts_ok, h6_G1. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I].
      split; [apply (h6_af _ _ _ _ _ E18); unfold SHADOW_OFF; lia|].
      split; [apply (h6_af _ _ _ _ _ E24); lia|].
      split; [apply (h6_af _ _ _ _ _ E25); lia|].
      split; [apply (h6_af _ _ _ _ _ E34); lia | exact I]. }
  assert (SHOK : sh_ok rsegs h6_Bx [] E1 (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs (h6_extra vb F (bv_unsigned b))) E1) by (subst E1; apply env_agree_refl).
  clear HE1 Hdc.
  (* 0x81880 .. 0x818c0: the two checks and the byte's load *)
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK h6_Bspan H6_CK.
  { apply (obl_of_range rsegs (w_H W) memc _ h6_Bx _ _ W6C_T6 16 Hra6).
    - apply (U_atom _ 18 SHADOW_OFF E18). unfold SHADOW_OFF. lia.
    - rewrite (h6_U_tbl _ _ E34 Ht). pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)). lia.
    - rewrite (h6_U_tbl _ _ E34 Ht). pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)). unfold W6C_T6. lia. }
  { apply (obl_of_range rsegs (w_H W) memc _ h6_Bx _ _ c (Z.of_nat (length (b :: r1))) Hrain).
    - apply (U_atom _ 18 SHADOW_OFF E18). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 25 c E25) by lia. lia.
    - rewrite (U_atom _ 25 c E25) by lia. lia. }
  { awr_ok_tac. }
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (h6_keep0 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KEall end.
  h6_ke F W U9.
  lazymatch type of KEall with forall a, aview _ _ ?m1 a = _ =>
    pose proof (rtm_rom_kept rsegs W W memc m1 Hrom (fun a _ => KEall a)) as Hrom1 end.
  clear KEall.
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (h6_extra vb F (bv_unsigned b))) Ex) by env_agree_chain HAE;
    assert (X9 : ew Ex 9 = Z_to_bv 64 R) by (rewrite ?ew_ewset_other by lia; exact E9);
    assert (X14 : ew Ex 14 = Z_to_bv 64 (c - 1)) by (rewrite ?ew_ewset_other by lia; exact E14);
    assert (X15 : ew Ex 15 = Z_to_bv 64 (Z.of_nat (length (b :: r1)) + 1)) by (rewrite ?ew_ewset_other by lia; exact E15);
    assert (X25 : ew Ex 25 = Z_to_bv 64 c) by (rewrite ?ew_ewset_other by lia; exact E25);
    assert (X32 : ew Ex 32 = Z_to_bv 64 vb) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (X33 : ew Ex 33 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other by lia; exact E33);
    assert (X34 : ew Ex 34 = Z_to_bv 64 (bv_unsigned b)) by (rewrite ?ew_ewset_other by lia; exact E34);
    remember Ex as E2 eqn:HE2
  end.
  clear HE2 HAE E9 E14 E15 E18 E24 E25 E32 E33 E34 U9 U25 SHOK.
  assert (V9 : bv_unsigned (ew E2 9) = R) by (rewrite X9; apply unsigned_lit_small; lia).
  assert (V33 : bv_unsigned (ew E2 33) = F) by (rewrite X33; apply unsigned_lit_small; lia).
  (* at 0x818c0: a2 = t & 3 and a0 = 0x211c0 + 4 (t & 3) *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (G12 : getr (ms_regs msx) (12%bv : bv 5) = Z_to_bv 64 (bv_unsigned b mod 4))
      by (h6_regv HS; rewrite denot_lit_U, (h6_U_and3 _ _ X34 Ht); reflexivity);
    assert (G10 : getr (ms_regs msx) (10%bv : bv 5) = Z_to_bv 64 (W6C_T6 + 4 * (bv_unsigned b mod 4)))
      by (h6_regv HS; rewrite denot_lit_U, (h6_U_tbl _ _ X34 Ht); reflexivity)
  end.
  pose proof HJ as (HAR1 & _).
  destruct (al_frames _ _ LAWS lyc Sc W _ _ 3 pos HAR1 Hin3) as (_ & _ & Hfp & _).
  rewrite <- HFa in Hfp. change (fs_frame_bytes 3) with 512 in Hfp.
  pose proof (h6_e_tbl B lyc Sc W memc mdc pos LAWS HAR Hin3) as HET. rewrite <- HFa in HET.
  clear HAR1 HAR.
  pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)) as Hm4.
  assert (Hj : bv_unsigned b mod 4 = 0 \/ bv_unsigned b mod 4 = 1 \/ bv_unsigned b mod 4 = 2 \/
               bv_unsigned b mod 4 = 3) by lia.
  destruct Hj as [Hj|[Hj|[Hj|Hj]]].
  all: lazymatch type of Hj with _ = ?j =>
    let TY := eval vm_compute in (nth (Z.to_nat j) Tables.t6 0) in
    let SZ := eval vm_compute in (w6c_sz6 TY) in
    assert (Hty : w6c_ty6 (bv_unsigned b) = TY) by (unfold w6c_ty6; rewrite Hj; reflexivity);
    assert (Hsz : w6c_sz6 TY = SZ) by reflexivity;
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
      assert (HS2 : st_ok rsegs E2 (h6_ss2 ssx j) (restrict (w_H W) msx));
      [ unfold h6_ss2; apply h6_reseat; [exact HS | reflexivity | |];
        [ apply regs_ok_pin;
          [ apply regs_ok_pin;
            [ exact (st_ok_regs_ok rsegs _ _ _ HS)
            | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X
            | change (ms_regs (restrict (w_H W) msx)) with (ms_regs msx); rewrite G12, Hj; reflexivity ]
          | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X
          | change (ms_regs (restrict (w_H W) msx)) with (ms_regs msx); rewrite G10, Hj; reflexivity ]
        | pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HRs & _);
          change (ms_mem (restrict (w_H W) msx)) with (mrestrict (w_H W) (ms_mem msx)) in HRs |- *;
          split; [vm_compute; reflexivity|]; split;
          [ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]];
            [ unfold h6_rE; apply (rtm_rw_region rsegs _ (w_H W) (ms_mem msx) 33%nat F);
              [exact V33 | lia | lia | intros o Ho; exact (proj1 (Hfp (F + o) ltac:(lia))) | constructor]
            | unfold h6_rT; apply (img_region_ok_rom _ W (ms_mem msx) W6C_T6 16);
              [exact Hrom1 | unfold W6C_T6; lia | unfold W6C_T6; lia | lia | vm_compute; reflexivity]
            | apply (proj1 (Forall_forall _ _) HRs); vm_compute; left; reflexivity
            | apply (proj1 (Forall_forall _ _) HRs); vm_compute; right; left; reflexivity ]
          | cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint, h6_rE, h6_rT, h6_rC1, h6_rC2;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite V9, V33; unfold W6C_T6 in HET |- *;
            repeat split; lia ] ]
      | clear HS; rename HS2 into HS ]
    end
  end.
  (* 0x818c0 .. the `bltu` 0x81cbc *)
  all: (aj_run_to w6c_tbl_ok HS HJ W6C_CPY; [h6_awr V33 HFa Hown pos|]).
  all: h6_ke F W V33.
  all: srr_branch_sh w6c_tbl_ok HS.
  all: h6_hc E2 X15 Hc.
  (* .. 0x51860 *)
  all: (aj_run_to w6c_tbl_ok HS HJ W6C_CPY; [h6_awr V33 HFa Hown pos|]).
  all: h6_ke F W V33.
  all: h6_leaf W HAE2.
  all: rewrite Hty, Hsz.
  all: lazymatch type of Hty with _ = ?TY => lazymatch type of Hsz with _ = ?SZ => h6_q HS V33 TY SZ end end.
Qed.
End b.

Print Assumptions w6c_h6.
