From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_y4s_iface RF_huf_y4fin.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition U4_CTZ : list Z :=
  [0; 1; 2; 7; 3; 13; 8; 19; 4; 25; 14; 28; 9; 34; 20; 40; 5; 17; 26; 38; 15; 46; 29; 48; 10; 31; 35; 54; 21; 50; 41; 57;
   63; 6; 12; 18; 24; 27; 33; 39; 16; 37; 45; 47; 30; 53; 49; 56; 62; 11; 23; 32; 36; 44; 52; 55; 61; 22; 43; 51; 60; 42; 59; 58].
Lemma u4_ctz_rd : forall m1 i, mem_inv usegs m1 -> 0 <= i < 64 ->
  exists b, ov_read_bytes usegs m1 (Z_to_bv 64 (0x104a0 + i)) 1 = Some [Z_to_bv 8 b] /\ 0 <= b <= 63.
Proof.
  intros m1 i MI Hi.
  assert (RB : ro_bytes_b usegs 0x104a0 (map (Z_to_bv 8) U4_CTZ) = true) by (vm_compute; reflexivity).
  assert (BA : bytes_at usegs m1 0x104a0 (map (Z_to_bv 8) U4_CTZ))
    by (apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn; lia | apply ro_bytes_b_sound; exact RB]).
  exists (Znth i U4_CTZ). split.
  - exact (src_rd usegs m1 0x104a0 U4_CTZ i BA ltac:(cbn; lia)).
  - assert (FA : Forall (fun x => 0 <= x <= 63) U4_CTZ) by (repeat constructor; lia).
    apply (proj1 (Forall_forall _ _) FA). unfold Znth. apply nth_In. cbn. lia.
Qed.
Lemma u4_shr58_bound : forall y, 0 <= y < 2^64 -> 0 <= y ≫ 58 < 64.
Proof.
  intros y Hy. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia|]. change (2^58 * 64) with (2^64). lia.
Qed.
Ltac pctz :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  lazymatch goal with MI : mem_inv usegs m |- _ =>
    let a := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common.STRW_tac.cur_mem_addr in
    lazymatch a with Z_to_bv 64 ?e =>
      lazymatch e with context [?y ≫ 58] =>
        let YB := fresh "YB" in let CR := fresh "CR" in let cz := fresh "cz" in let CZ := fresh "CZ" in
        pose proof (u4_shr58_bound y ltac:(first [apply Z.mod_pos_bound; lia | lia])) as YB;
        let CR := fresh "RSRC" in
        destruct (u4_ctz_rd m (e - 0x104a0) MI ltac:(lia)) as (cz & CR & CZ);
        replace (0x104a0 + (e - 0x104a0)) with e in CR by ring
      end
    end
  end end.

Lemma p_shl3 : forall x, x ≪ 3 = 8 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Ltac y5stop pc := lazymatch pc with 0x16824 => idtac | 0x16a44 => idtac | 0x16d6c => idtac end.
Ltac y5tgt pc := lazymatch pc with 0x16e58 => idtac | 0x16e18 => idtac | 0x16e34 => idtac | 0x16e48 => idtac end.
Ltac y5step := try (rewrite ?y4_srl3 by lia); try (rewrite ?p_shl3);
  first [zstep | y4src; zstep; y4clr | pctz; zstep; y4clr]; try y4gen.
Ltac y5after U := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      tryif y5tgt pc then (exfalso; y4pbU U; lia) else (try (exfalso; y4pbU U; lia))
  | _ => idtac end.
Ltac y5drive := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif y5stop pc then fail else (tryif y5tgt pc then fail else y5step)
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let U := fresh "U" in if_cases U; try (y4pz U); try (change (2 ^ 2) with 4 in U); try (y5after U)
  | _ => y5step end).
Ltac y5mod := repeat (match goal with |- context [?x mod 18446744073709551616] =>
  rewrite (Z.mod_small x 18446744073709551616) by lia end).
Ltac y5side := first [ lia | rewrite byte_lit by lia; lia ].

Definition y4_se (DST dcap prev : Z) : Z :=
  if DST + dcap - prev <? (dcap + 3) / 4 then DST + dcap else prev + (dcap + 3) / 4.

Section CANSEC1. Context {rc : runConstT}.
Section Y4F5.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Hypothesis TOK : x2_table_ok cells 11.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 8192.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis SG : 3 * seg < dcap.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis DTA : DT mod 4 = 0.
  Hypothesis CBL : DT + 4 + 8192 <= lo.
  Hypothesis DJ1 : DT + 4 + 8192 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation Y4M := (RF_huf_y4s_iface.Y4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation SPS4 := (RF_huf_y4s_iface.SPS4 DST dcap SS DT src).

  Notation YF l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
                      TOK ECB LCB D8 DC SG DL S0 SL NSM BYS DT0 DTA CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  Notation NDT := (Z.lxor (DT + 4) 18446744073709551615).
  Notation KH pc mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 prev) x9 (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 64)
             (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation STB pc mm k SE OPk p ptr bits c x1 x7 x17 x21 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) x17 (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) (Z_to_bv 64 p) c x26 x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation ELB pc mm k SE OPk ptr bits c x1 x7 x21 x24 x27 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -512)) gp tp (Z_to_bv 64 65) (Z_to_bv 64 2) x7 (Z_to_bv 64 SE) (Z_to_bv 64 OPk) (Z_to_bv 64 k)
             (Z_to_bv 64 (SP + -264)) (Z_to_bv 64 0x104a0) (Z_to_bv 64 NDT) (Z_to_bv 64 (SP + -384)) (Z_to_bv 64 9)
             (Z_to_bv 64 0x218a392cd3d5dbf) (Z_to_bv 64 8) (Z_to_bv 64 ptr) (Z_to_bv 64 SS) (Z_to_bv 64 (SS + 8)) x21 (Z_to_bv 64 bits)
             (Z_to_bv 64 SE) x24 c (Z_to_bv 64 (SE - OPk)) x27 (Z_to_bv 64 64) (Z_to_bv 64 ((dcap + 3) ≫ 2)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (SP + -352 + 8 * k)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Section BODY.
  Variables (k prev IPk OPk IEk : Z) (Bk : word) (w0 w8 w64 w72 w80 w88 w96 w104 w112 : Z) (ws ops ips bts : list word).
  Notation SEp := (y4_se DST dcap prev).
  Notation SPSk := (SPS4 w0 w8 w64 w72 w80 w88 w96 w104 w112).
  Hypothesis K4 : 0 <= k < 4.
  Hypothesis HPV : DST <= prev <= DST + dcap.
  Hypothesis WS13 : nth_error ws 13 = Some (Z_to_bv 64 SS).
  Hypothesis WIP : nth_error ws (Z.to_nat k) = Some (Z_to_bv 64 IPk).
  Hypothesis WOP : nth_error ws (Z.to_nat (4 + k)) = Some (Z_to_bv 64 OPk).
  Hypothesis WBK : nth_error ws (Z.to_nat (8 + k)) = Some Bk.
  Hypothesis WIE : nth_error ws (Z.to_nat (15 + k)) = Some (Z_to_bv 64 IEk).
  Hypothesis HOP : DST <= OPk <= DST + dcap.
  Hypothesis HIP : SS <= IPk /\ IPk + 8 <= SS + n.
  Hypothesis HIE : SS <= IEk <= SS + n.
  Hypothesis HBK : bv_unsigned Bk <> 0.

  Hypothesis EXL : forall mm bits (c x1 x7 x17 x21 x27 : word),
    Y4M mm SPSk ws ops ips bts -> OPk + 8 <= SEp -> 0 <= bits < 64 ->
    evt usegs POST (STB 0x16824 mm k SEp OPk OPk IPk bits c x1 x7 x17 x21 (Z_to_bv 64 (SEp + -9)) x27).
  Hypothesis EXE : forall mm bits (c x1 x7 x21 x24 x27 : word),
    Y4M mm SPSk ws ops ips bts -> OPk <= SEp -> SEp - OPk < 8 -> 0 <= bits < 64 ->
    evt usegs POST (ELB 0x16a44 mm k SEp OPk IPk bits c x1 x7 x21 x24 x27).

  Lemma y4f_body : forall mm (x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
    Y4M mm SPSk ws ops ips bts ->
    evt usegs POST (KH 0x16720 mm k prev x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31).
  Proof using All.
    intros mm x1 x7 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 Y.
    pose proof Y as Y0.
    destruct Y0 as ((buf & ARR & LB) & SRC & CBR & STK & SPA & SPL & WSA & WSL & (jo & JO) & OPA & OPL & IPA & IPL & BTA & BTL
                    & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
    pose proof (bv_unsigned_in_range 64 Bk) as RBK; unfold bv_modulus in RBK; cbn in RBK.
    assert (SGL : 0 <= (dcap + 3) / 4 <= dcap) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    assert (SHR : (dcap + 3) ≫ 2 = (dcap + 3) / 4) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    pose proof (u64arr_read usegs mm (SP + -384) ws k (Z_to_bv 64 IPk) (wa (SP + -384 + 8 * k)) WSA WIP ltac:(lia) eq_refl) as RIP.
    pose proof (u64arr_read usegs mm (SP + -384) ws (4 + k) (Z_to_bv 64 OPk) (wa (SP + -352 + 8 * k)) WSA WOP ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as ROP.
    pose proof (u64arr_read usegs mm (SP + -384) ws (8 + k) Bk (wa (SP + -320 + 8 * k)) WSA WBK ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RBKr.
    pose proof (u64arr_read usegs mm (SP + -384) ws (15 + k) (Z_to_bv 64 IEk) (wa (SP + -264 + 8 * k)) WSA WIE ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RIE.
    pose proof (u64arr_read usegs mm (SP + -384) ws 13 (Z_to_bv 64 SS) (wa (SP + -280)) WSA WS13 ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RSS.
    pose proof (u64arr_read usegs mm (SP + -512) _ 7 (Z_to_bv 64 (DST + dcap)) (wa (SP + -512 + 8 * 7)) SPA eq_refl ltac:(lia) eq_refl) as RSP7.
    pose proof EXL as EXL'. pose proof EXE as EXE'.
    destruct (Z.ltb_spec (DST + dcap - prev) ((dcap + 3) / 4)) as [HS|HS].
    - assert (ESE : SEp = DST + dcap) by (unfold y4_se; destruct (Z.ltb_spec (DST + dcap - prev) ((dcap + 3) / 4)); lia).
      rewrite ESE in EXL', EXE'.
      y5drive.
      all: y5mod.
      all: first [ solve [eapply EXE'; [exact Y | y5side ..]]
                 | solve [eapply EXL'; [exact Y | y5side ..]]
                 | solve [eapply (YF y4_err); exact Y] ].
    - assert (ESE : SEp = (dcap + 3) ≫ 2 + prev) by (unfold y4_se; destruct (Z.ltb_spec (DST + dcap - prev) ((dcap + 3) / 4)); lia).
      rewrite ESE in EXL', EXE'.
      y5drive.
      all: y5mod.
      all: first [ solve [eapply EXE'; [exact Y | y5side ..]]
                 | solve [eapply EXL'; [exact Y | y5side ..]]
                 | solve [eapply (YF y4_err); exact Y] ].
  Qed.

  End BODY.
End Y4F5.
End CANSEC1.
