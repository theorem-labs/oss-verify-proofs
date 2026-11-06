(** reac-pw/fuzz_segconf, UBSan build (image 1696d6c34ffd, unstripped twin afc060e3cc9c): piece P8 of
    reac_segconf_parse_file, the ignore key (reac_segconf.c:271-280, with parse_bool R:88-99 inlined). Proves
    [pf_p8_holds : strcasecmp_contract -> S_P8] (lib/U/Prog/reac_segconf_parse_file_pieces_c.v): IGN -> KREF (the
    refusal F_badignore) or PROV (ignore = b, ignore_set = 1). The UBSan twin of lib/Prog/pf_p8.v,
    written new.

    Code (the UBSan binary):
      0x15798 .. 0x157a4 strcasecmp(val = s7, "yes" 0x1042f); 0x157a8 s4 = 1; 0x157ac beqz a0 -> 0x15b20
      0x157b0 .. 0x157bc strcasecmp(val, "true" 0x10517); 0x157c0 beqz a0 -> 0x15b20
      0x157c4 s6 = val[0]; 0x157cc bne s6, '1' -> 0x157d8; 0x157d0 a0 = val[1]; 0x157d4 beqz a0 -> 0x15b20
      0x157d8 .. 0x157e4 strcasecmp(val, "no" 0x10711); 0x157e8 beqz a0 -> 0x15b1c
      0x157ec .. 0x157f8 strcasecmp(val, "false" 0x1029d); 0x157fc beqz a0 -> 0x15b1c
      0x15800 a0 = '0'; 0x15804 bne s6, a0 -> 0x15810; 0x15808 a0 = val[1]; 0x1580c beqz a0 -> 0x15b1c
      0x15810 a2 = F_badignore 0x10714; 0x15818 j KREF 0x158f0
      0x15b1c s4 = 0; 0x15b20 a0 = cur (the slot sp + 0x88); 0x15b24 andi a0, a0, 3; 0x15b28 bnez a0 -> trap 0x15c7c
      (refuted: cur = c + 356 gi, c mod 16 = 0, 356 = 4 * 89); 0x15b2c a0 = cur; 0x15b30 sw s4, 0x18(a0) (ignore);
      0x15b34 sw s11 = 1, 0x1c(a0) (ignore_set); 0x15b38 a0 = cur + 0x100; 0x15b40 a2 = "%s" 0x104e0;
      0x15b44 j PROV 0x15b70
    The spine and the six tests are the plain walk's (lib/Prog/pf_p8_lemmas.v). strcasecmp writes only
    [sp - 32, sp); the two stores write seg[gi] + 0x18 .. 0x20 of the c block (p8_rconf_ign). The context goes across
    both by U/Prog/pfC_facts.pfc_ctx_call, cur's slot by pfc_curslot_call, and each exit cut's post comes back to the
    entry memory by pfC_facts.pf_fin_weaken. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import tolower_c strcasecmp_c pfC_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_p8_lemmas.
Import ListNotations.
Open Scope Z_scope.

(** ** This build's tolower and the four literals in .rodata *)
Lemma p8u_tolower : forall c, 0 <= c < 256 -> zlower c = SegModel.tolower c.
Proof.
  intros c Hc.
  assert (H : forallb (fun z => Z.eqb (zlower z) (SegModel.tolower z)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma p8_ro_yes : ro_bytes_b rsegs 0x1042f (zb S_yes ++ [ZERO]) = true. Proof. vm_compute. reflexivity. Qed.
Lemma p8_ro_true : ro_bytes_b rsegs 0x10517 (zb S_true ++ [ZERO]) = true. Proof. vm_compute. reflexivity. Qed.
Lemma p8_ro_no : ro_bytes_b rsegs 0x10711 (zb S_no ++ [ZERO]) = true. Proof. vm_compute. reflexivity. Qed.
Lemma p8_ro_false : ro_bytes_b rsegs 0x1029d (zb S_false ++ [ZERO]) = true. Proof. vm_compute. reflexivity. Qed.
Lemma p8_bv_yes : p8_byte_vals S_yes. Proof. apply p8_bv_lit. vm_compute. reflexivity. Qed.
Lemma p8_bv_true : p8_byte_vals S_true. Proof. apply p8_bv_lit. vm_compute. reflexivity. Qed.
Lemma p8_bv_no : p8_byte_vals S_no. Proof. apply p8_bv_lit. vm_compute. reflexivity. Qed.
Lemma p8_bv_false : p8_byte_vals S_false. Proof. apply p8_bv_lit. vm_compute. reflexivity. Qed.

Ltac p8_zle := apply Z.leb_le; vm_compute; reflexivity.

Section Walk.
Hypothesis HSC : strcasecmp_contract.
Variables (n : nat) (sp gp tp s0 s1 s2 s3 s5 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat)
  (ln : Z) (d : list (list Z)) (gi : nat) (cur vp : Z) (val : list Z).
Hypothesis HKREF : H_KREF n.
Hypothesis HPROV : H_PROV n.
Hypothesis Hregs : pf_regs s0 s1 s2 s3 s5 s10 (Z_to_bv 64 1) (t + Z.of_nat (pf_next s o)) (ln + 1).
Hypothesis Hinb : pf_inb (bv_unsigned sp + PF_BUF) vp val.
Hypothesis Hcur : cur = rseg_addr c gi.
Hypothesis Hnz : ~ In 0 val.
Hypothesis Hvb : forall x, In x val -> 0 <= x < 256.
Hypothesis Hspine : r_key rc (Some gi) nm (ln + 1) (pf_tline s o) =
  match parse_bool val with
  | None => (refuse rc (ln + 1) F_badignore [AS nm; AS val], Some gi, nm)
  | Some b => (pf_prov_fin (PIgn b) rc gi, Some gi, nm)
  end.

(** The entry's post (H_IGN's). *)
Definition POST : machine_state -> Prop :=
  pf_fin v sp gp tp F m0 lo c
    (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))).

(** What holds of the memory at every pc of the piece before the stores: the cut context, c holding rc, cur in its
    slot, the value val in buf, and the change from the entry memory inside the function's W. *)
Definition INV (m : word -> option byte) : Prop :=
  pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n /\
  pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) /\
  pf_curslot m (bv_unsigned sp) c (Some gi) /\
  cstr_at rsegs m vp val /\ munch (pfc_W (bv_unsigned sp) c) m0 m /\ wmono rsegs m0 m.

Lemma inv_env : forall m, INV m ->
  0 <= lo /\ lo + 6032 <= bv_unsigned sp /\ bv_unsigned sp + 0x420 <= 2 ^ 64 /\
  (c + SEG_C_SIZE <= lo \/ bv_unsigned sp + 0x420 <= c) /\ 0x54088 <= lo.
Proof.
  intros m (HC & _). destruct HC as (HE & _).
  destruct (pfc_env_lo _ _ _ _ _ _ HE) as (H1 & H2 & H3 & H4 & H5 & _). unfold apart in H4. tauto.
Qed.

(** strcasecmp writes only its frame [sp - 32, sp). *)
Lemma inv_call : forall m m', INV m -> munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> INV m'.
Proof.
  intros m m' HI MU WM MI ST.
  destruct (inv_env m HI) as (Hlo0 & Hlo & Hsp & Hap & Himg).
  destruct HI as (HC & (HR & HOK & HNM & HCN) & HCS & HV & MU0 & WM0).
  pose proof HC as (HE & _).
  pose proof HE as (_ & _ & _ & _ & (FRM & TM & _) & _ & (STK & _) & _).
  pose proof Hinb as [Hb1 Hb2]. unfold PF_BUF in Hb1, Hb2.
  assert (NO : forall x, ~ outside [(bv_unsigned sp - 32, bv_unsigned sp)] x -> bv_unsigned sp - 32 <= x < bv_unsigned sp)
    by (intros x; apply p8_not_out1).
  assert (OUT : forall x, ~ (bv_unsigned sp - 32 <= x < bv_unsigned sp) -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] x)
    by (intros x; apply p8_out1).
  assert (TM' : MemNorm.task_mem rsegs m').
  { apply (pfc_task_mem_munch _ m m' TM MU). intros x Hx. apply NO in Hx.
    destruct STK as (_ & _ & STa).
    destruct (STa (bv_unsigned x) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (b & Hb)].
    unfold wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
  split; [|split; [|split; [|split; [|split]]]].
  - apply (pfc_ctx_call m m' fc fc (bv_unsigned sp) lo v c t s o ln d n _ HC MU WM);
      [| | exact ST | exact MI | exact TM' | exact FRM].
    + apply pfc_fw_low. intros x Hx. left. apply NO in Hx. lia.
    + intros x Hx Ho. apply NO in Ho. exfalso. unfold pfc_scr, PF_CURSLOT, PF_SAVE in Hx. lia.
  - split; [|split; [exact HOK|split; [|exact HCN]]].
    + apply (pfc_rconf_munch _ m m' c rc HR MU). intros x Hx. apply OUT. unfold SEG_C_SIZE in *. lia.
    + apply (pfc_nm_call m m' fc (bv_unsigned sp) lo c v nm _ HE HNM MU). intros x Hx. apply OUT.
      unfold PF_NAMEBUF in Hx. lia.
  - apply (pfc_curslot_call m m' fc (bv_unsigned sp) lo c v (Some gi) _ HE HCS MU). intros x Hx. apply OUT.
    unfold PF_CURSLOT in Hx. lia.
  - apply (pfc_cstr_munch _ m m' vp val HV MU). intros x Hx. apply OUT. lia.
  - apply (munch_trans _ m0 m m' MU0). apply (munch_weaken [(bv_unsigned sp - 32, bv_unsigned sp)]); [|exact MU].
    intros x Hx. unfold pfc_W in Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. apply OUT.
    unfold PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in Hx. lia.
  - exact (wmono_trans rsegs _ _ _ WM0 WM).
Qed.

(** One call strcasecmp(val, lit) (the literal at L in .rodata), with the return address rt: the context is kept and
    a0 = 0 exactly when val and lit are equal after the fold. *)
Lemma sc_call : forall (Q : machine_state -> Prop) (lit : list Z) (L rt : Z) m
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
  INV m -> p8_byte_vals lit -> ro_bytes_b rsegs L (zb lit ++ [ZERO]) = true ->
  0 <= L -> L + Z.of_nat (length lit) + 1 <= 0x54088 -> 0 <= rt < 2 ^ 64 -> rt mod 2 = 0 ->
  (forall m' r (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word), INV m' ->
     (r = Z_to_bv 64 0 <-> SegModel.strcasecmp val lit = 0) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 rt) sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
       (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 rt) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 rt) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 vp) (Z_to_bv 64 L) a2 a3 a4 a5 a6 a7
       s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 STRCASECMP) fc None m
       (seg_rom rsegs)).
Proof.
  intros Q lit L rt m t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 HI HL HRO HL0 HL1 Hrt Hev K.
  destruct (inv_env m HI) as (Hlo0 & Hlo & Hsp & Hap & Himg).
  pose proof HI as (HC & HS & HCS & HV & MU0 & WM0).
  pose proof HC as (HE & _).
  pose proof HE as (_ & _ & _ & _ & _ & _ & (STK & _) & MI & _).
  pose proof Hinb as [Hb1 Hb2]. unfold PF_BUF in Hb1, Hb2.
  pose proof HV as (bs & sl & B & Hz & Hn & Hsl).
  assert (Hlen : length bs = length val) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  assert (NB : ~ In (Z_to_bv 8 0) bs) by (apply p8_nul_free_bytes; rewrite Hz; exact Hn).
  assert (BV : bytes_at rsegs m vp (bs ++ [Z_to_bv 8 0])).
  { replace (bs ++ ZERO :: sl) with ((bs ++ [ZERO]) ++ sl) in B by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in B. exact (proj1 B). }
  assert (Llen : length (zb lit) = length lit) by (unfold zb; apply length_map).
  assert (BL : bytes_at rsegs m L (zb lit ++ [Z_to_bv 8 0])).
  { apply pfc_ro_str; [exact MI | exact HL0 | rewrite length_app, Llen; cbn [length]; lia | exact HRO]. }
  pose proof HSC as SC. unfold strcasecmp_contract in SC.
  eapply evt_cut.
  { eapply (SC (Z_to_bv 64 rt) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 vp) (Z_to_bv 64 L) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
      s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6 F fc m bs (zb lit) lo).
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) STK
                     ltac:(unfold PARSE_FILE_FRAME; lia))).
    - rewrite unsigned_lit by lia. exact BV.
    - exact NB.
    - rewrite unsigned_lit by lia. exact BL.
    - exact (p8_zb_nonul lit HL).
    - exact MI.
    - lia.
    - right. rewrite unsigned_lit by lia. lia.
    - left. rewrite unsigned_lit by lia. rewrite Llen. lia. }
  intros ms' (r & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              -> & MU & WM & MI' & ST' & _ & _ & HR).
  rewrite (ret_pc_even rt Hrt Hev).
  apply K.
  - exact (inv_call m m' HI MU WM MI' ST').
  - unfold lower_eq, zb in HR. rewrite (p8_lower_eq zlower p8u_tolower bs lit NB HL) in HR.
    rewrite Hz in HR. exact HR.
Qed.

(** The bytes val[0] and val[1] (`lbu` at 0x157c4, 0x157d0, 0x15808). *)
Lemma val_b0 : forall m, INV m -> ov_read_bytes rsegs m (wa (vp + 0)) 1 = Some [Z_to_bv 8 (nth 0 val 0)].
Proof. intros m (_ & _ & _ & HV & _). exact (p8_cstr_byte rsegs m vp val 0 HV (Nat.le_0_l _)). Qed.

Lemma val_b1 : forall m x, INV m -> 0 < x -> nth 0 val 0 = x ->
  ov_read_bytes rsegs m (wa (vp + 1)) 1 = Some [Z_to_bv 8 (nth 1 val 0)].
Proof.
  intros m x (_ & _ & _ & HV & _) Hx H. exact (p8_cstr_byte rsegs m vp val 1 HV (p8_len1 val x Hx H)).
Qed.

(** KREF (0x158f0): parse_bool val = None, the refusal F_badignore with cur_name and val. *)
Lemma exit_kref : forall m (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
  INV m -> parse_bool val = None ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 PF_STR_BADIGNORE) a3 a4 a5 a6 a7 s2 s3 s4 s5
    s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 PF_PC_KREF) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 (HC & HS & HCS & HV & MU0 & WM0) HN.
  eapply evt_mono.
  - exact (HKREF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 PF_STR_BADIGNORE) a3 a4 a5 a6 a7 s2 s3 s4 s5
             s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6 F fc m lo v c t s rc (Some gi) nm o ln d
             F_badignore PF_STR_BADIGNORE vp val HC HS Hregs HCS
             ltac:(right; left; reflexivity) eq_refl eq_refl HV Hinb).
  - intros ms HP. unfold POST. rewrite Hspine, HN.
    exact (pf_fin_weaken v sp gp tp F F m0 m lo c _ ms HP MU0 WM0 (fun k _ => eq_refl)).
Qed.

(** PROV (0x15b70): parse_bool val = Some b, c holding pf_prov_mid (PIgn b), a0 = the ignore_file field. *)
Lemma exit_prov : forall b m (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
  pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
  pf_state m (bv_unsigned sp) c (pf_prov_mid (PIgn b) rc gi) (Some gi) nm (length (skipn o s)) ->
  pf_curslot m (bv_unsigned sp) c (Some gi) ->
  munch (pfc_W (bv_unsigned sp) c) m0 m -> wmono rsegs m0 m -> parse_bool val = Some b ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cur + 256)) a1 (Z_to_bv 64 PF_STR_S) a3 a4 a5 a6
    a7 s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 PF_PC_PROV) fc None m
    (seg_rom rsegs)).
Proof.
  intros b m ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 HC HS HCS MU0 WM0 HB.
  eapply evt_mono.
  - exact (HPROV ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cur + 256)) a1 (Z_to_bv 64 PF_STR_S) a3 a4 a5 a6 a7 s2 s3 s4
             s5 s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6 F fc m lo v c t s rc nm o ln d (PIgn b) gi
             HC HS Hregs HCS ltac:(rewrite Hcur; reflexivity) eq_refl).
  - intros ms HP. unfold POST. rewrite Hspine, HB.
    exact (pf_fin_weaken v sp gp tp F F m0 m lo c _ ms HP MU0 WM0 (fun k _ => eq_refl)).
Qed.

(** The memories after the two stores. *)
Definition M1 (m : word -> option byte) (b : bool) : word -> option byte :=
  write_to_mem m (Z_to_bv 64 (cur + 24)) (le4 (Z_to_bv 64 (b2z b))).
Definition M2 (m : word -> option byte) (b : bool) : word -> option byte :=
  write_to_mem (M1 m b) (Z_to_bv 64 (cur + 28)) (le4 (Z_to_bv 64 1)).

Lemma inv_store : forall m b, INV m ->
  store_ok rsegs m (wa (cur + 24)) 4 = true /\ store_ok rsegs (M1 m b) (wa (cur + 28)) 4 = true /\
  pf_ctx (M2 m b) fc (bv_unsigned sp) lo v c t s o ln d n /\
  pf_state (M2 m b) (bv_unsigned sp) c (pf_prov_mid (PIgn b) rc gi) (Some gi) nm (length (skipn o s)) /\
  pf_curslot (M2 m b) (bv_unsigned sp) c (Some gi) /\
  munch (pfc_W (bv_unsigned sp) c) m0 (M2 m b) /\ wmono rsegs m0 (M2 m b).
Proof.
  intros m b HI.
  destruct (inv_env m HI) as (Hlo0 & Hlo & Hsp & Hap & Himg).
  destruct HI as (HC & (HR & HOK & HNM & HCN) & HCS & HV & MU0 & WM0).
  pose proof HC as (HE & _).
  pose proof HE as (_ & _ & _ & Hni & (FRM & TM & _) & _ & (STK & _) & MI & _).
  pose proof HR as (bs & HB & HEnc).
  pose proof HEnc as (HL & H32 & _).
  unfold pf_cur_ok in HOK.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  unfold SEG_C_SIZE in HL, Hap.
  assert (Ecur : cur = c + 356 * Z.of_nat gi) by (rewrite Hcur; unfold rseg_addr, RSEG_SIZE; lia).
  pose proof (pfc_c_wr m c rc HR Hni) as WR.
  assert (HS1 : store_ok rsegs m (wa (cur + 24)) 4 = true).
  { pose proof (wr_at_store_ok rsegs m c SEG_C_SIZE (356 * Z.of_nat gi + 24) 4 WR ltac:(lia)
                  ltac:(unfold SEG_C_SIZE; lia)) as X.
    replace (c + (356 * Z.of_nat gi + 24)) with (cur + 24) in X by lia. exact X. }
  assert (HS2 : store_ok rsegs (M1 m b) (wa (cur + 28)) 4 = true).
  { pose proof (wr_at_write rsegs m c SEG_C_SIZE (Z_to_bv 64 (cur + 24)) (le4 (Z_to_bv 64 (b2z b))) WR) as WR1.
    pose proof (wr_at_store_ok rsegs _ c SEG_C_SIZE (356 * Z.of_nat gi + 28) 4 WR1 ltac:(lia)
                  ltac:(unfold SEG_C_SIZE; lia)) as X.
    replace (c + (356 * Z.of_nat gi + 28)) with (cur + 28) in X by lia. exact X. }
  assert (HB2 : bytes_at rsegs (M2 m b) c (upd_bytes bs (356 * gi + 24) (p8_ign_bytes b))).
  { pose proof (bytes_at_write_inside rsegs m c bs (Z.of_nat (356 * gi + 24)) (le4 (Z_to_bv 64 (b2z b))) HB
                  ltac:(lia) ltac:(rewrite Nat2Z.id, length_le4; lia)) as X1.
    rewrite Nat2Z.id in X1.
    replace (c + Z.of_nat (356 * gi + 24)) with (cur + 24) in X1 by lia.
    assert (Lb : (356 * gi + 24 + 4 + 4 <= length bs)%nat) by lia.
    assert (Lx : (Z.to_nat (Z.of_nat (356 * gi + 24 + 4)) + length (le4 (Z_to_bv 64 1)) <=
                  length (upd_bytes bs (356 * gi + 24) (le4 (Z_to_bv 64 (b2z b)))))%nat).
    { rewrite Nat2Z.id. rewrite upd_bytes_length by (rewrite length_le4; lia). rewrite length_le4. exact Lb. }
    pose proof (bytes_at_write_inside rsegs _ c _ (Z.of_nat (356 * gi + 24 + 4)) (le4 (Z_to_bv 64 1)) X1
                  ltac:(lia) Lx) as X2.
    rewrite Nat2Z.id in X2.
    replace (c + Z.of_nat (356 * gi + 24 + 4)) with (cur + 28) in X2 by lia.
    replace (356 * gi + 24 + 4)%nat with (356 * gi + 24 + length (le4 (Z_to_bv 64 (b2z b))))%nat in X2
      by (rewrite length_le4; reflexivity).
    rewrite p8_upd_upd in X2 by (rewrite !length_le4; lia).
    exact X2. }
  assert (HR2 : rconf_at rsegs (M2 m b) c (pf_prov_mid (PIgn b) rc gi)).
  { exists (upd_bytes bs (356 * gi + 24) (p8_ign_bytes b)). split; [exact HB2|].
    exact (p8_rconf_ign rc bs gi b HEnc HOK). }
  assert (MU : munch [(cur + 24, cur + 32)] m (M2 m b)).
  { unfold M2, M1.
    apply munch_write; [ | lia | rewrite length_le4; lia | cbn [inside]; left; rewrite length_le4; lia].
    apply munch_write; [ | lia | rewrite length_le4; lia | cbn [inside]; left; rewrite length_le4; lia].
    apply munch_refl. }
  assert (WM : wmono rsegs m (M2 m b)).
  { unfold M2, M1. apply wmono_write. apply wmono_write. apply wmono_refl. }
  assert (NO : forall x, ~ outside [(cur + 24, cur + 32)] x -> cur + 24 <= x < cur + 32)
    by (intros x; apply p8_not_out1).
  assert (OUT : forall x, ~ (cur + 24 <= x < cur + 32) -> outside [(cur + 24, cur + 32)] x)
    by (intros x; apply p8_out1).
  assert (ST : stk rsegs (M2 m b) lo (bv_unsigned sp)).
  { unfold M2, M1.
    apply stk_write; [ | lia | rewrite length_le4; lia].
    apply stk_write; [ | lia | rewrite length_le4; lia].
    exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) STK
                    ltac:(unfold PARSE_FILE_FRAME; lia))). }
  assert (MI2 : mem_inv rsegs (M2 m b)).
  { unfold M2. apply mem_inv_store; [ | rewrite length_le4; exact HS2].
    unfold M1. apply mem_inv_store; [exact MI | rewrite length_le4; exact HS1]. }
  assert (TM2 : MemNorm.task_mem rsegs (M2 m b)).
  { apply (pfc_task_mem_munch _ m _ TM MU). intros x Hx. apply NO in Hx.
    apply (p8_bytes_present rsegs m c bs x HB). rewrite HL. lia. }
  split; [exact HS1|]. split; [exact HS2|].
  split; [|split; [|split; [|split]]].
  - apply (pfc_ctx_call m (M2 m b) fc fc (bv_unsigned sp) lo v c t s o ln d n _ HC MU WM);
      [| | exact ST | exact MI2 | exact TM2 | exact FRM].
    + apply pfc_fw_low. intros x Hx. right. apply NO in Hx. unfold SEG_C_SIZE. lia.
    + intros x Hx Ho. apply NO in Ho. exfalso. unfold pfc_scr, PF_CURSLOT, PF_SAVE in Hx. lia.
  - split; [exact HR2|]. split; [exact (pfc_cur_ok_upd rc gi _ (Some gi) HOK)|].
    split; [|exact (pfc_cnt_upd rc gi _ _ _ HCN (le_n _))].
    apply (pfc_nm_call m (M2 m b) fc (bv_unsigned sp) lo c v nm _ HE HNM MU). intros x Hx. apply OUT.
    unfold PF_NAMEBUF, PF_SAVE in Hx. lia.
  - apply (pfc_curslot_call m (M2 m b) fc (bv_unsigned sp) lo c v (Some gi) _ HE HCS MU). intros x Hx. apply OUT.
    unfold PF_CURSLOT in Hx. lia.
  - apply (munch_trans _ m0 m _ MU0). apply (munch_weaken [(cur + 24, cur + 32)]); [|exact MU].
    intros x Hx. unfold pfc_W, RC_PARSE_W in Hx. cbn [outside] in Hx. destruct Hx as (_ & Hx & _). apply OUT.
    unfold RC_N in Hx. lia.
  - exact (wmono_trans rsegs _ _ _ WM0 WM).
Qed.

(** cur from its slot, 4-aligned. *)
Lemma cur_facts : forall m, INV m ->
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 136)) 8 = Some (le8 (Z_to_bv 64 cur)) /\
  0 <= cur < 2 ^ 64 /\ cur mod 4 = 0.
Proof.
  intros m HI. destruct (inv_env m HI) as (Hlo0 & Hlo & Hsp & Hap & Himg).
  destruct HI as (HC & (HR & HOK & _) & HCS & _).
  pose proof HC as (HE & _). pose proof HE as (_ & Hc16 & _).
  pose proof HR as (bs & HB & HEnc). pose proof HEnc as (HL & H32 & _). unfold pf_cur_ok in HOK.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  assert (Ecur : cur = c + 356 * Z.of_nat gi) by (rewrite Hcur; unfold rseg_addr, RSEG_SIZE; lia).
  split; [|split].
  - pose proof (pfc_ld_cur m (bv_unsigned sp) c (Some gi) HCS) as X. unfold PF_CURSLOT in X.
    cbn [pf_cur_ptr] in X. rewrite <- Hcur in X. exact X.
  - unfold SEG_C_SIZE in HL. lia.
  - rewrite Ecur. Z.div_mod_to_equations. lia.
Qed.

(** 0x15b20: cur from its slot, the alignment test, the two stores and the jump to PROV. *)
Lemma at_store : forall b m (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word),
  INV m -> parse_bool val = Some b ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (b2z b)) s5 s6
    (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 0x15b20) fc None m (seg_rom rsegs)).
Proof.
  intros b m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 HI HB.
  destruct (cur_facts m HI) as (HRc & Hcr & H4).
  destruct (inv_store m b HI) as (HS1 & HS2 & HC2 & HS2' & HCS2 & MU2 & WM2).
  unfold M1 in HS2.
  step. step. step. if_cases KA.
  - exfalso. rewrite (p8_and3 cur Hcr H4) in KA. rewrite bv_eqb_refl in KA. cbn [negb] in KA. discriminate KA.
  - step. step. step. step. step. step. step.
    apply (exit_prov b (M2 m b)); assumption.
Qed.

(** 0x15b1c: s4 = 0 (false), then the stores. *)
Lemma at_false : forall m (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
  INV m -> parse_bool val = Some false ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
    (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 0x15b1c) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 HI HB.
  step. apply (at_store false m); assumption.
Qed.

(** 0x157d8: "yes", "true" and "1" have failed; "no", "false", "0". s6 holds val[0]. *)
Lemma from_no : forall m (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
  INV m -> SegModel.strcasecmp val S_yes <> 0 -> SegModel.strcasecmp val S_true <> 0 -> strcmp val [49] <> 0 ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
    (zxb (Z_to_bv 8 (nth 0 val 0))) (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 0x157d8) fc
    None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 HI Hy Ht H1.
  pose proof (p8_nth_val val 0 Hvb) as X0.
  pose proof (p8_nth_val val 1 Hvb) as X1.
  step. step. step. step.
  eapply (sc_call _ S_no); [exact HI | exact p8_bv_no | exact p8_ro_no | lia | p8_zle | lia | reflexivity |].
  intros m1 r1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HI1 HR1.
  step. if_cases K1.
  - apply p8_eqb_t in K1. apply HR1 in K1.
    apply (at_false m1); [exact HI1|]. apply p8_pb_false; [exact Hy | exact Ht | exact H1 | left; exact K1].
  - apply p8_eqb_f in K1.
    assert (Hn' : SegModel.strcasecmp val S_no <> 0) by (intros E; apply K1; apply HR1; exact E).
    step. step. step. step.
    eapply (sc_call _ S_false); [exact HI1 | exact p8_bv_false | exact p8_ro_false | lia | p8_zle | lia | reflexivity |].
    intros m2 r2 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' HI2 HR2.
    step. if_cases K2.
    + apply p8_eqb_t in K2. apply HR2 in K2.
      apply (at_false m2); [exact HI2|]. apply p8_pb_false; [exact Hy | exact Ht | exact H1 | right; left; exact K2].
    + apply p8_eqb_f in K2.
      assert (Hf' : SegModel.strcasecmp val S_false <> 0) by (intros E; apply K2; apply HR2; exact E).
      step. step. if_cases K3.
      * (* val[0] <> '0': the refusal *)
        apply Bool.negb_true_iff in K3. pose proof (p8_byte_ne _ _ K3 X0) as K3'.
        assert (H0' : strcmp val [48] <> 0).
        { intros E. apply (proj1 (p8_strcmp1 val 48 Hnz ltac:(lia))) in E. apply K3'. rewrite E. reflexivity. }
        step. step. step.
        apply (exit_kref m2); [exact HI2 | apply p8_pb_none; auto].
      * apply Bool.negb_false_iff in K3. pose proof (p8_byte_eq _ _ K3 X0 ltac:(lia)) as K3'.
        pose proof (val_b1 m2 48 HI2 ltac:(lia) K3') as HRb.
        step. step. if_cases K4.
        -- (* val = "0" *)
           pose proof (p8_byte_eq _ _ K4 X1 ltac:(lia)) as K4'.
           apply (at_false m2); [exact HI2|]. apply p8_pb_false; [exact Hy | exact Ht | exact H1 |]. right. right.
           apply (proj2 (p8_strcmp1 val 48 Hnz ltac:(lia))). apply (proj2 (p8_one_byte val 48 Hnz ltac:(lia) K3')).
           exact K4'.
        -- pose proof (p8_byte_ne _ _ K4 X1) as K4'.
           assert (H0' : strcmp val [48] <> 0).
           { intros E. apply (proj1 (p8_strcmp1 val 48 Hnz ltac:(lia))) in E. apply K4'.
             apply (proj1 (p8_one_byte val 48 Hnz ltac:(lia) K3')). exact E. }
           step. step. step.
           apply (exit_kref m2); [exact HI2 | apply p8_pb_none; auto].
Qed.

(** The piece from IGN (0x15798). *)
Lemma walk : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word), INV m0 ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
    (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6) F (Z_to_bv 64 PF_PC_IGN) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 HI. unfold PF_PC_IGN.
  pose proof (p8_nth_val val 0 Hvb) as X0.
  pose proof (p8_nth_val val 1 Hvb) as X1.
  step. step. step. step.
  eapply (sc_call _ S_yes); [exact HI | exact p8_bv_yes | exact p8_ro_yes | lia | p8_zle | lia | reflexivity |].
  intros m1 r1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HI1 HR1.
  step. step. if_cases K1.
  - apply p8_eqb_t in K1. apply HR1 in K1.
    apply (at_store true m1); [exact HI1 | exact (p8_pb_yes val K1)].
  - apply p8_eqb_f in K1.
    assert (Hy : SegModel.strcasecmp val S_yes <> 0) by (intros E; apply K1; apply HR1; exact E).
    step. step. step. step.
    eapply (sc_call _ S_true); [exact HI1 | exact p8_bv_true | exact p8_ro_true | lia | p8_zle | lia | reflexivity |].
    intros m2 r2 t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' HI2 HR2.
    step. if_cases K2.
    + apply p8_eqb_t in K2. apply HR2 in K2.
      apply (at_store true m2); [exact HI2 | exact (p8_pb_true val K2)].
    + apply p8_eqb_f in K2.
      assert (Ht : SegModel.strcasecmp val S_true <> 0) by (intros E; apply K2; apply HR2; exact E).
      pose proof (val_b0 m2 HI2) as HRb0.
      step. step. step. if_cases K3.
      * (* val[0] <> '1' *)
        apply Bool.negb_true_iff in K3. pose proof (p8_byte_ne _ _ K3 X0) as K3'.
        apply (from_no m2); [exact HI2 | exact Hy | exact Ht |].
        intros E. apply (proj1 (p8_strcmp1 val 49 Hnz ltac:(lia))) in E. apply K3'. rewrite E. reflexivity.
      * apply Bool.negb_false_iff in K3. pose proof (p8_byte_eq _ _ K3 X0 ltac:(lia)) as K3'.
        pose proof (val_b1 m2 49 HI2 ltac:(lia) K3') as HRb1.
        step. step. if_cases K4.
        -- (* val = "1" *)
           pose proof (p8_byte_eq _ _ K4 X1 ltac:(lia)) as K4'.
           apply (at_store true m2); [exact HI2|]. apply p8_pb_one.
           apply (proj2 (p8_strcmp1 val 49 Hnz ltac:(lia))). apply (proj2 (p8_one_byte val 49 Hnz ltac:(lia) K3')).
           exact K4'.
        -- pose proof (p8_byte_ne _ _ K4 X1) as K4'.
           apply (from_no m2); [exact HI2 | exact Hy | exact Ht |].
           intros E. apply (proj1 (p8_strcmp1 val 49 Hnz ltac:(lia))) in E. apply K4'.
           apply (proj1 (p8_one_byte val 49 Hnz ltac:(lia) K3')). exact E.
Qed.

End Walk.

Theorem pf_p8_holds : strcasecmp_contract -> S_P8.
Proof.
  intros HSC n HK HP. unfold H_IGN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v
    c t s rc nm o ln d gi kp vp key val HC HS HRg HCS HKV H8 H7 HR1 HR2 HR3.
  destruct HKV as ((ei & Hei & Hk & Hv) & _ & _ & HVc & HVi).
  pose proof HRg as (_ & _ & _ & _ & _ & _ & E11).
  subst s7 s11.
  pose proof (p8_spine rc gi nm (ln + 1) (pf_tline s o) ei key val Hei Hk Hv HR1 HR2 HR3) as Hsp.
  pose proof HVc as (bs & sl & _ & _ & Hn & _).
  pose proof (p8_cstr_vals rsegs m vp val HVc) as Hvb.
  eapply walk with (cur := rseg_addr c gi); try eassumption; try reflexivity.
  split; [exact HC|]. split; [exact HS|]. split; [exact HCS|]. split; [exact HVc|].
  split; [apply munch_refl | apply wmono_refl].
Qed.
