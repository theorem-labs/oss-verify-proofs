(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pck I_pcbits I_pcseg I_pchead I_pcdint.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pcrr I_pcdstr I_pcfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_pcxa I_pcxdir I_pcxchk F_achk I_pcxprec I_pcxchk2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require I_vsnstmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.




Import I_vsnstmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcx_flags_app : forall s, exists fs, s = fs ++ pcx_flags s /\ Forall (fun f => f = 45 \/ f = 48) fs.
Proof.
  induction s as [|c s IH]; [exists []; split; [reflexivity| constructor]|].
  cbn [pcx_flags]. unfold pcx_isflag. destruct (Z.eqb_spec c 45) as [E|NE]; [| destruct (Z.eqb_spec c 48) as [E2|NE2]]; cbn [orb].
  - destruct IH as (fs & E1 & F1). exists (c :: fs). split; [cbn; rewrite <- E1; reflexivity| constructor; [lia| exact F1]].
  - destruct IH as (fs & E1 & F1). exists (c :: fs). split; [cbn; rewrite <- E1; reflexivity| constructor; [lia| exact F1]].
  - exists []. split; [reflexivity| constructor].
Qed.
Lemma pcx_flags_hd : forall s c t, pcx_flags s = c :: t -> c <> 45 /\ c <> 48.
Proof.
  induction s as [|x s IH]; intros c t H; [discriminate|]. cbn [pcx_flags] in H. unfold pcx_isflag in H.
  destruct (Z.eqb_spec x 45); [| destruct (Z.eqb_spec x 48)]; cbn [orb] in H; [exact (IH _ _ H)| exact (IH _ _ H)|]. injection H as <- <-. lia.
Qed.
Lemma pcx_digits_app : forall s, exists ds, s = ds ++ pcx_digits s /\ Forall is_digit ds.
Proof.
  induction s as [|c s IH]; [exists []; split; [reflexivity| constructor]|].
  cbn [pcx_digits]. unfold pcx_isdigit. destruct (Z.leb_spec 48 c); [destruct (Z.leb_spec c 57)|]; cbn [andb].
  - destruct IH as (ds & E1 & F1). exists (c :: ds). split; [cbn; rewrite <- E1; reflexivity| constructor; [unfold is_digit; lia| exact F1]].
  - exists []. split; [reflexivity| constructor].
  - exists []. split; [reflexivity| constructor].
Qed.
Lemma pcx_digits_hd : forall s c t, pcx_digits s = c :: t -> ~ is_digit c.
Proof.
  induction s as [|x s IH]; intros c t H; [discriminate|]. cbn [pcx_digits] in H. unfold pcx_isdigit in H.
  destruct (Z.leb_spec 48 x); [destruct (Z.leb_spec x 57)|]; cbn [andb] in H; [exact (IH _ _ H)| |]; injection H as <- <-; unfold is_digit; lia.
Qed.
Lemma pcx_conv_inv : forall lm c k, pcx_conv lm c = Some k ->
  pcx_cconv c /\
  match k with
  | PK_str => c = 115 /\ lm = false | PK_char => c = 99 /\ lm = false
  | PK_int => pcx_iconv c /\ lm = false | PK_long => pcx_iconv c /\ lm = true
  end.
Proof.
  intros lm c k H. unfold pcx_conv in H. unfold pcx_cconv, pcx_iconv.
  destruct (Z.eqb_spec c 100); [| destruct (Z.eqb_spec c 105); [| destruct (Z.eqb_spec c 117); [| destruct (Z.eqb_spec c 120); [| destruct (Z.eqb_spec c 88)]]]];
    cbn [orb] in H.
  1-5: destruct lm; injection H as <-; split; lia.
  destruct lm; [discriminate|]. destruct (Z.eqb_spec c 99); [injection H as <-; split; lia|].
  destruct (Z.eqb_spec c 115); [injection H as <-; split; lia| discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition plcase (pp : pcx_prec) (pl : list Z) : Prop :=
  match pp with
  | PP_none => pl = []
  | PP_star => pl = [46; 42]
  | PP_num => exists d ds, pl = 46 :: d :: ds /\ is_digit d /\ Forall is_digit ds
  end.

Lemma pcx_precp_inv : forall s pp s3, pcx_precp s = Some (pp, s3) ->
  exists pl, s = pl ++ s3 /\ plcase pp pl /\ (pp <> PP_none -> forall c t, s3 = c :: t -> ~ is_digit c) /\ (pp = PP_star -> s3 <> []).
Proof.
  intros s pp s3 H. unfold pcx_precp in H.
  destruct s as [|c0 s0]; [injection H as <- <-; exists []; split; [reflexivity|]; split; [reflexivity|]; split; [intros X; exfalso; apply X; reflexivity| intros X; discriminate X]|].
  destruct (Z.eq_dec c0 46) as [->|N46].
  - destruct s0 as [|c1 s1].
    + discriminate H.
    + destruct (Z.eq_dec c1 42) as [->|N42].
      * destruct s1 as [|c2 s2]; [discriminate H|]. unfold pcx_isdigit in H.
        destruct (Z.leb_spec 48 c2); [destruct (Z.leb_spec c2 57)|]; cbn [andb] in H; try discriminate H;
          injection H as <- <-; exists [46; 42]; (split; [reflexivity|]); (split; [reflexivity|]);
          (split; [intros _ c t E; injection E as <- _; unfold is_digit; lia| intros _; discriminate]).
      * assert (H' : match c1 :: s1 with
                     | c :: _ => if pcx_isdigit c then Some (PP_num, pcx_digits (c1 :: s1)) else None
                     | [] => None end = Some (pp, s3)).
        { destruct c1 as [|pp1|pp1]; try exact H. repeat (destruct pp1 as [pp1|pp1|]; try exact H). exfalso. apply N42. reflexivity. }
        clear H. unfold pcx_isdigit in H'. destruct (Z.leb_spec 48 c1); [destruct (Z.leb_spec c1 57)|]; cbn [andb] in H'; try discriminate H'.
        injection H' as <- <-.
        replace (if pcx_isdigit c1 then pcx_digits s1 else c1 :: s1) with (pcx_digits s1)
          by (unfold pcx_isdigit; rewrite (proj2 (Z.leb_le 48 c1)) by lia; rewrite (proj2 (Z.leb_le c1 57)) by lia; reflexivity).
        destruct (pcx_digits_app s1) as (ds1 & Eds & Fds).
        exists (46 :: c1 :: ds1). split; [cbn; rewrite <- Eds; reflexivity|].
        split; [exists c1, ds1; split; [reflexivity| split; [unfold is_digit; lia| exact Fds]]|].
        split; [| intros X; discriminate X]. intros _ c t E. exact (pcx_digits_hd _ _ _ E).
  - assert (H' : Some (PP_none, c0 :: s0) = Some (pp, s3)).
    { destruct c0 as [|pp0|pp0]; try exact H. repeat (destruct pp0 as [pp0|pp0|]; try exact H). exfalso. apply N46. reflexivity. }
    injection H' as <- <-. exists []. split; [reflexivity|]. split; [reflexivity|]. split; [intros X; exfalso; apply X; reflexivity| intros X; discriminate X].
Qed.

Lemma pcx_dir_inv : forall s ws pp k rest, pcx_dir s = Some (ws, pp, k, rest) ->
  exists fs wl pl ll cv,
    s = fs ++ wl ++ pl ++ ll ++ cv :: rest
    /\ Forall (fun f => f = 45 \/ f = 48) fs
    /\ ((ws = true /\ wl = [42]) \/ (ws = false /\ wl = []) \/ (ws = false /\ exists d ds, wl = d :: ds /\ is_digit d /\ Forall is_digit ds))
    /\ notin_flags (hd 0 (wl ++ pl ++ ll ++ [cv]))
    /\ plcase pp pl
    /\ (ll = [] \/ ll = [108])
    /\ pcx_conv (match ll with [] => false | _ => true end) cv = Some k
    /\ ~ is_digit (hd 0 (pl ++ ll ++ [cv]))
    /\ (wl = [] -> hd 0 (pl ++ ll ++ [cv]) <> 42)
    /\ (pp <> PP_none -> k = PK_str).
Proof.
  intros s ws pp k rest H. unfold pcx_dir in H.
  destruct (pcx_flags_app s) as (fs & Es & Ffs). set (s1 := pcx_flags s) in *.
  assert (CV : forall lm cv, pcx_conv lm cv = Some k -> ~ is_digit cv /\ cv <> 42 /\ notin_flags cv /\ (cv <> 108) /\ cv <> 46).
  { intros lm cv Hc. destruct (pcx_conv_inv lm cv k Hc) as [CC _]. unfold pcx_cconv in CC. unfold is_digit, notin_flags. lia. }
  assert (LEN : forall s3 (ws0 : bool) (pp0 : pcx_prec),
    (let '(lm, s4) := match s3 with 108 :: s' => (true, s') | _ => (false, s3) end in
     match s4 with
     | c :: s5 => match pcx_conv lm c with
                  | Some k0 => match pp0, k0 with PP_none, _ => Some (ws0, pp0, k0, s5) | _, PK_str => Some (ws0, pp0, k0, s5) | _, _ => None end
                  | None => None end
     | [] => None end) = Some (ws, pp, k, rest) ->
    exists ll cv, s3 = ll ++ cv :: rest /\ ws0 = ws /\ pp0 = pp /\ (ll = [] \/ ll = [108]) /\ pcx_conv (match ll with [] => false | _ => true end) cv = Some k
                  /\ ~ is_digit (hd 0 (ll ++ [cv])) /\ hd 0 (ll ++ [cv]) <> 42 /\ notin_flags (hd 0 (ll ++ [cv])) /\ (pp <> PP_none -> k = PK_str)).
  { intros s3 ws0 pp0 HH. destruct s3 as [|c2 s4]; [discriminate|].
    assert (PK : forall (lm : bool) c s5,
      match pcx_conv lm c with
      | Some k0 => match pp0, k0 with PP_none, _ => Some (ws0, pp0, k0, s5) | _, PK_str => Some (ws0, pp0, k0, s5) | _, _ => None end
      | None => None end = Some (ws, pp, k, rest) -> pcx_conv lm c = Some k /\ ws0 = ws /\ pp0 = pp /\ s5 = rest /\ (pp <> PP_none -> k = PK_str)).
    { intros lm c s5 E. destruct (pcx_conv lm c) as [k0|]; [| discriminate E].
      destruct pp0, k0; try discriminate E; injection E as <- <- <- <-; repeat split; try reflexivity; intros X; try reflexivity; exfalso; apply X; reflexivity. }
    destruct (Z.eq_dec c2 108) as [->|NE].
    - destruct s4 as [|c3 s5]; [discriminate|]. destruct (PK true c3 s5 HH) as (PC & <- & <- & -> & KS).
      exists [108], c3. destruct (CV _ _ PC) as (A1 & A2 & A3 & A4 & A5).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|]. split; [exact PC|]. cbn [hd app].
      split; [unfold is_digit; lia|]. split; [lia|]. split; [unfold notin_flags; lia| exact KS].
    - assert (HH' : match pcx_conv false c2 with
                     | Some k0 => match pp0, k0 with PP_none, _ => Some (ws0, pp0, k0, s4) | _, PK_str => Some (ws0, pp0, k0, s4) | _, _ => None end
                     | None => None end = Some (ws, pp, k, rest)).
      { destruct c2 as [|p2|p2]; try exact HH. repeat (destruct p2 as [p2|p2|]; try exact HH). exfalso. apply NE. reflexivity. }
      destruct (PK false c2 s4 HH') as (PC & <- & <- & -> & KS).
      exists [], c2. destruct (CV _ _ PC) as (A1 & A2 & A3 & A4 & A5).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity|]. split; [exact PC|]. cbn [hd app].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3| exact KS]. }
  (* [comment removed for export] *)
  assert (PRE : forall s2 (ws0 : bool),
    match pcx_precp s2 with
    | None => None
    | Some (pp0, s3) =>
        (let '(lm, s4) := match s3 with 108 :: s' => (true, s') | _ => (false, s3) end in
         match s4 with
         | c :: s5 => match pcx_conv lm c with
                      | Some k0 => match pp0, k0 with PP_none, _ => Some (ws0, pp0, k0, s5) | _, PK_str => Some (ws0, pp0, k0, s5) | _, _ => None end
                      | None => None end
         | [] => None end)
    end = Some (ws, pp, k, rest) ->
    exists pl ll cv, s2 = pl ++ ll ++ cv :: rest /\ ws0 = ws /\ plcase pp pl /\ (ll = [] \/ ll = [108]) /\ pcx_conv (match ll with [] => false | _ => true end) cv = Some k
                     /\ ~ is_digit (hd 0 (pl ++ ll ++ [cv])) /\ hd 0 (pl ++ ll ++ [cv]) <> 42 /\ notin_flags (hd 0 (pl ++ ll ++ [cv])) /\ (pp <> PP_none -> k = PK_str)).
  { intros s2 ws0 HH. destruct (pcx_precp s2) as [[pp0 s3]|] eqn:PP; [| discriminate HH].
    destruct (LEN s3 ws0 pp0 HH) as (ll & cv & -> & <- & <- & LL & PC & ND & N42 & NF & KS).
    destruct (pcx_precp_inv _ _ _ PP) as (pl & -> & PL & _ & _).
    exists pl, ll, cv. split; [reflexivity|]. split; [reflexivity|]. split; [exact PL|]. split; [exact LL|]. split; [exact PC|].
    destruct pp0; cbn in PL.
    - subst pl. cbn [app]. split; [exact ND|]. split; [exact N42|]. split; [exact NF| exact KS].
    - destruct PL as (d & ds & -> & _ & _). cbn. unfold is_digit, notin_flags. split; [lia|]. split; [lia|]. split; [lia| exact KS].
    - subst pl. cbn. unfold is_digit, notin_flags. split; [lia|]. split; [lia|]. split; [lia| exact KS]. }
  rewrite Es. destruct s1 as [|c1 t1] eqn:S1.
  - cbn in H. discriminate H.
  - pose proof (pcx_flags_hd s c1 t1 S1) as [N45 N48].
    destruct (Z.eq_dec c1 42) as [->|N42].
    + destruct (PRE t1 true H) as (pl & ll & cv & -> & <- & PL & LL & PC & ND & N42' & NF & KS).
      exists fs, [42], pl, ll, cv. split; [reflexivity|]. split; [exact Ffs|]. split; [left; split; reflexivity|].
      split; [cbn; unfold notin_flags; lia|]. split; [exact PL|]. split; [exact LL|]. split; [exact PC|].
      split; [exact ND|]. split; [intros X; discriminate X| exact KS].
    + assert (H' : match pcx_precp (pcx_digits (c1 :: t1)) with
                   | None => None
                   | Some (pp0, s3) =>
                       (let '(lm, s4) := match s3 with 108 :: s' => (true, s') | _ => (false, s3) end in
                        match s4 with
                        | c :: s5 => match pcx_conv lm c with
                                     | Some k0 => match pp0, k0 with PP_none, _ => Some (false, pp0, k0, s5) | _, PK_str => Some (false, pp0, k0, s5) | _, _ => None end
                                     | None => None end
                        | [] => None end)
                   end = Some (ws, pp, k, rest)).
      { destruct c1 as [|p1|p1]; try exact H. repeat (destruct p1 as [p1|p1|]; try exact H). exfalso. apply N42. reflexivity. }
      clear H. destruct (pcx_digits_app (c1 :: t1)) as (ds & Eds & Fds).
      destruct (PRE (pcx_digits (c1 :: t1)) false H') as (pl & ll & cv & Ell & <- & PL & LL & PC & ND & N42' & NF & KS).
      exists fs, ds, pl, ll, cv.
      split; [rewrite Eds at 1; rewrite Ell; rewrite <- ?app_assoc; reflexivity|]. split; [exact Ffs|].
      destruct ds as [|d ds'].
      * cbn in Eds. split; [right; left; split; reflexivity|]. split; [cbn [app]; exact NF|].
        split; [exact PL|]. split; [exact LL|]. split; [exact PC|]. split; [exact ND|]. split; [intros _; exact N42'| exact KS].
      * apply Forall_cons_iff in Fds. destruct Fds as [Fd Fds'].
        cbn in Eds. injection Eds as <- Eds'.
        split; [right; right; split; [reflexivity| exists c1, ds'; split; [reflexivity| split; [exact Fd| exact Fds']]]|].
        split; [cbn; unfold notin_flags; unfold is_digit in Fd; lia|].
        split; [exact PL|]. split; [exact LL|]. split; [exact PC|]. split; [exact ND|]. split; [intros X; discriminate X| exact KS].
Qed.

(* [comment removed for export] *)
Fixpoint dsplit (l : list Z) : list Z * list Z :=
  match l with [] => ([], []) | c :: t => if pcx_isdigit c then let (a, b) := dsplit t in (c :: a, b) else ([], l) end.
Lemma dsplit_app : forall l1 x l2, ~ is_digit x ->
  exists a b, l1 = a ++ b /\ Forall is_digit a /\ (forall c t, b ++ x :: l2 = c :: t -> ~ is_digit c) /\ dsplit (l1 ++ x :: l2) = (a, b ++ x :: l2).
Proof.
  induction l1 as [|c l1 IH]; intros x l2 NX.
  - exists [], []. split; [reflexivity|]. split; [constructor|]. split; [intros c t E; cbn in E; injection E as <- _; exact NX|].
    cbn [app dsplit]. unfold pcx_isdigit. unfold is_digit in NX. destruct (Z.leb_spec 48 x); [destruct (Z.leb_spec x 57)|]; cbn [andb]; first [reflexivity | exfalso; lia].
  - destruct (IH x l2 NX) as (a & b & E & FA & HB & DS).
    cbn [app dsplit]. unfold pcx_isdigit. destruct (Z.leb_spec 48 c); [destruct (Z.leb_spec c 57)|]; cbn [andb].
    + rewrite DS. exists (c :: a), b. split; [cbn; rewrite E; reflexivity|]. split; [constructor; [unfold is_digit; lia| exact FA]|]. split; [exact HB| reflexivity].
    + exists [], (c :: l1). split; [reflexivity|]. split; [constructor|]. split; [intros c0 t E0; cbn in E0; injection E0 as <- _; unfold is_digit; lia| reflexivity].
    + exists [], (c :: l1). split; [reflexivity|]. split; [constructor|]. split; [intros c0 t E0; cbn in E0; injection E0 as <- _; unfold is_digit; lia| reflexivity].
Qed.

Lemma zb8_split : forall m p l1 l2, bytes_at ctasegs m p (zb8 (l1 ++ l2)) ->
  bytes_at ctasegs m p (zb8 l1) /\ bytes_at ctasegs m (p + Z.of_nat (length l1)) (zb8 l2).
Proof.
  intros m p l1 l2 BY. rewrite zb8_app in BY. apply (proj1 (bytes_at_app ctasegs m p _ _)) in BY. rewrite length_zb8 in BY. exact BY.
Qed.
Lemma zb8_prefix : forall m p l1 l2, bytes_at ctasegs m p (zb8 (l1 ++ l2)) -> bytes_at ctasegs m p (zb8 l1).
Proof. intros m p l1 l2 BY. exact (proj1 (zb8_split m p l1 l2 BY)). Qed.

Lemma zb8_window_hd : forall m p l1 l2 x l3, bytes_at ctasegs m p (zb8 (l1 ++ l2 ++ x :: l3)) ->
  bytes_at ctasegs m (p + Z.of_nat (length l1)) (zb8 (l2 ++ [x])).
Proof.
  intros m p l1 l2 x l3 BY. apply zb8_split in BY. destruct BY as [_ BY].
  apply (zb8_prefix m _ (l2 ++ [x]) l3). rewrite <- app_assoc. cbn [app]. exact BY.
Qed.
Lemma hd_app_ne : forall (l : list Z) x r d, hd d (l ++ x :: r) = hd d (l ++ [x]).
Proof. intros l x r d. destruct l; reflexivity. Qed.
Lemma hd_app2_ne : forall (l1 l2 : list Z) x r d, hd d (l1 ++ l2 ++ x :: r) = hd d (l1 ++ l2 ++ [x]).
Proof. intros l1 l2 x r d. destruct l1; [destruct l2|]; reflexivity. Qed.
Lemma hd_app3_ne : forall (l1 l2 l3 : list Z) x r d, hd d (l1 ++ l2 ++ l3 ++ x :: r) = hd d (l1 ++ l2 ++ l3 ++ [x]).
Proof. intros l1 l2 l3 x r d. destruct l1; [destruct l2; [destruct l3|]|]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ck_arg (m : mem) (lo q : Z) (w : word) (a : parg) (cov : option Z) : Prop :=
  match a with
  | PA_s _ => match cov with
              | Some _ => True
              | None => exists str : list byte, cstr_at m (bv_unsigned w) str /\ 0 < bv_unsigned w
                          /\ (bv_unsigned w + Z.of_nat (length str) + 1 <= lo \/ q <= bv_unsigned w)
                          /\ bv_unsigned w + Z.of_nat (length str) + 1 < 2^47 /\ chkr m (bv_unsigned w) (Z.of_nat (length str) + 1)
              end
  | PA_sn => bv_unsigned w = 0
  | _ => True
  end.
Fixpoint ck_args (m : mem) (lo q : Z) (slots : list word) (args : list parg) (covs : list (option Z)) : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with [] => False | w :: slots' => ck_arg m lo q w a (vhd_cov covs) /\ ck_args m lo q slots' args' (tl covs) end
  end.

Definition ckW (q : Z) : list (Z * Z) := [(q + -2320, q + -2240); (q + -2216, q + -2176)].

Lemma ck_arg_agree : forall m m' lo q w a cov, ck_arg m lo q w a cov -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo ->
  agree_on (fun x => x < q + -2320 \/ q <= x) m m' -> ck_arg m' lo q w a cov.
Proof.
  intros m m' lo q w a cov H LO LOLO AG. unfold kHighShadowEnd in LOLO. destruct a; cbn [ck_arg] in H |- *; try exact H.
  destruct cov as [cv|]; [exact I|].
  destruct H as (str & CS & P0 & SEP & HI & CK). exists str. split; [| split; [exact P0| split; [exact SEP| split; [exact HI|]]]].
  - apply (cstr_agree m m' _ _ CS). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn. lia.
  - apply (chkr_agree m m' _ _ CK). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn. unfold SHADOW_LO, SHADOW_HI in Hx. lia.
Qed.
Lemma ck_args_agree : forall m m' lo q slots args covs, ck_args m lo q slots args covs -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo ->
  agree_on (fun x => x < q + -2320 \/ q <= x) m m' -> ck_args m' lo q slots args covs.
Proof.
  intros m m' lo q slots args. revert slots. induction args as [|a args IH]; intros slots covs H LO LOLO AG; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [exact (ck_arg_agree _ _ _ _ _ _ _ H1 LO LOLO AG)| exact (IH _ _ H2 LO LOLO AG)].
Qed.

(* [comment removed for export] *)
Lemma ck_args_split : forall m lo q slots astar a args covs,
  ck_args m lo q slots (astar ++ a :: args) covs ->
  exists wstar w slots2, slots = wstar ++ w :: slots2 /\ length wstar = length astar
    /\ ck_arg m lo q w a (vhd_cov (skipn (length astar) covs)) /\ ck_args m lo q slots2 args (tl (skipn (length astar) covs)).
Proof.
  intros m lo q slots astar. revert slots. induction astar as [|a0 astar IH]; intros slots a args covs H.
  - cbn [app] in H. destruct slots as [|w slots2]; [destruct H|]. destruct H as [H1 H2]. exists [], w, slots2. repeat split; assumption.
  - cbn [app ck_args] in H. destruct slots as [|w0 slots1]; [destruct H|]. destruct H as [H0 H]. destruct (IH slots1 a args (tl covs) H) as (wstar & w & slots2 & -> & L & CA & CR).
    exists (w0 :: wstar), w, slots2. split; [reflexivity|]. split; [cbn; lia|]. cbn [length skipn]. destruct covs; cbn [tl skipn] in CA, CR |- *; [| split; assumption].
    rewrite skipn_nil in *. split; assumption.
Qed.

(* [comment removed for export] *)
Definition nstarsx (ws : bool) (pp : pcx_prec) : nat := ((if ws then 1 else 0) + (match pp with PP_star => 1 | _ => 0 end))%nat.
Definition owncov (pp : pcx_prec) (k : pcx_kind) (covs : list (option Z)) : option Z :=
  match pp, k with PP_star, PK_str => vhd_cov covs | _, _ => None end.
Lemma pcx_step_inv : forall fuel s' args cin ws pp k rest n,
  pcx_dir s' = Some (ws, pp, k, rest) -> pcx_walk (S fuel) (37 :: s') args = Some n ->
  exists astar a args3, args = astar ++ a :: args3 /\ length astar = nstarsx ws pp /\ pcx_fits k a = true
    /\ (exists n3, pcx_walk fuel rest args3 = Some n3 /\ n = (nstarsx ws pp + 1 + n3)%nat)
    /\ pcx_covs (S fuel) (37 :: s') args cin
       = repeat None (nstarsx ws pp) ++ owncov pp k (skipn (nstarsx ws pp) cin) :: pcx_covs fuel rest args3 (tl (skipn (nstarsx ws pp) cin)).
Proof.
  intros fuel s' args cin ws pp k rest n PD WK. cbn [pcx_walk] in WK. rewrite PD in WK. cbn [pcx_covs]. rewrite PD. change (37 =? 0) with false in *. change (37 =? 37) with true in *. cbn [negb andb orb] in WK |- *.
  destruct ws.
  - destruct args as [|a0 args1]; [discriminate WK|]. destruct pp.
    + destruct args1 as [|a args3]; [discriminate WK|]. destruct (pcx_fits k a) eqn:FT; [| discriminate WK]. destruct (pcx_walk fuel rest args3) as [n3|] eqn:W3; [| discriminate WK].
      injection WK as <-. exists [a0], a, args3. split; [reflexivity|]. split; [reflexivity|]. split; [exact FT|]. split; [exists n3; split; [first [exact W3 | reflexivity]| reflexivity]|].
      cbn. destruct cin as [|c0 cin1]; cbn; [| destruct cin1; cbn]; destruct k; reflexivity.
    + destruct args1 as [|a args3]; [discriminate WK|]. destruct (pcx_fits k a) eqn:FT; [| discriminate WK]. destruct (pcx_walk fuel rest args3) as [n3|] eqn:W3; [| discriminate WK].
      injection WK as <-. exists [a0], a, args3. split; [reflexivity|]. split; [reflexivity|]. split; [exact FT|]. split; [exists n3; split; [first [exact W3 | reflexivity]| reflexivity]|].
      cbn. destruct cin as [|c0 cin1]; cbn; [| destruct cin1; cbn]; destruct k; reflexivity.
    + destruct args1 as [|a1 args2]; [discriminate WK|]. destruct args2 as [|a args3]; [discriminate WK|]. destruct (pcx_fits k a) eqn:FT; [| discriminate WK].
      destruct (pcx_walk fuel rest args3) as [n3|] eqn:W3; [| discriminate WK].
      injection WK as <-. exists [a0; a1], a, args3. split; [reflexivity|]. split; [reflexivity|]. split; [exact FT|]. split; [exists n3; split; [first [exact W3 | reflexivity]| reflexivity]|].
      cbn. destruct cin as [|c0 [|c1 [|c2 cin3]]]; cbn; destruct k; reflexivity.
  - destruct pp.
    + destruct args as [|a args3]; [discriminate WK|]. destruct (pcx_fits k a) eqn:FT; [| discriminate WK]. destruct (pcx_walk fuel rest args3) as [n3|] eqn:W3; [| discriminate WK].
      injection WK as <-. exists [], a, args3. split; [reflexivity|]. split; [reflexivity|]. split; [exact FT|]. split; [exists n3; split; [first [exact W3 | reflexivity]| reflexivity]|].
      cbn. destruct cin as [|c0 cin1]; cbn; destruct k; reflexivity.
    + destruct args as [|a args3]; [discriminate WK|]. destruct (pcx_fits k a) eqn:FT; [| discriminate WK]. destruct (pcx_walk fuel rest args3) as [n3|] eqn:W3; [| discriminate WK].
      injection WK as <-. exists [], a, args3. split; [reflexivity|]. split; [reflexivity|]. split; [exact FT|]. split; [exists n3; split; [first [exact W3 | reflexivity]| reflexivity]|].
      cbn. destruct cin as [|c0 cin1]; cbn; destruct k; reflexivity.
    + destruct args as [|a1 args2]; [discriminate WK|]. destruct args2 as [|a args3]; [discriminate WK|]. destruct (pcx_fits k a) eqn:FT; [| discriminate WK].
      destruct (pcx_walk fuel rest args3) as [n3|] eqn:W3; [| discriminate WK].
      injection WK as <-. exists [a1], a, args3. split; [reflexivity|]. split; [reflexivity|]. split; [exact FT|]. split; [exists n3; split; [first [exact W3 | reflexivity]| reflexivity]|].
      cbn. destruct cin as [|c0 [|c1 cin2]]; cbn; destruct k; reflexivity.
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Definition pcx_ret_post (q lo : Z) (ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra0 (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom ctasegs)
    /\ munch (ckW q) m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (q + -2240)
    /\ (exists junk, rw_cells ctasegs m' (q + -2216) [CB 40 junk]).

(* [comment removed for export] *)
Lemma pcx_Lend_spec : forall (q p lo : Z) (junk : list byte) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 (q + -2240) -> s3 = Z_to_bv 64 p ->
  bytes_at ctasegs m p [z8] -> rw_cells ctasegs m (q + -2216) [CB 40 junk] ->
  rw_cells ctasegs m (q + -104) (pcom_saved ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11') ->
  stk ctasegs m lo (q + -2240) -> 2320 <= q -> q <= 2^47 -> mem_inv ctasegs m ->
  evt ctasegs (pcx_ret_post q lo ra0 gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1a64) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros -> -> B0 DJ SV ST QLO QHI MI. unfold pcom_saved in SV.
  pose proof (bytes_at_bound _ _ _ _ B0) as PB. cbn [length] in PB.
  pose proof (ro_C1_of_bytes m p _ B0) as CB0. clear B0.
  pose proof (munch_refl (ckW q) m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  lstep. lstep. br2 K.
  do 16 lstep.
  setreg 2%Z (Z_to_bv 64 q) ltac:(f_equal; lia).
  apply evt_done. unfold pcx_ret_post. do 16 eexists.
  split; [ first [reflexivity | f_equal; f_equal; f_equal; lia] |].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exists junk; exact DJ].
Qed.

(* [comment removed for export] *)
Local Ltac tr_fmt BY MU := apply (bytes_at_agree ctasegs _ _ _ _ BY); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
  rewrite ?length_zb8 in Hx; rewrite ?length_app in Hx; cbn [length] in Hx; rewrite ?length_app in Hx; cbn [length] in Hx; unfold ckW; out_lia.

(* [comment removed for export] *)
Theorem pcx_list_spec : forall (fuel : nat) (s : list Z) (args : list parg) (cin : list (option Z)) (n : nat) (q p ap lo : Z) (slots : list word)
    (ra0 sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 : word)
    ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  pcx_walk fuel s args = Some n ->
  bytes_at ctasegs m p (zb8 s) -> p + Z.of_nat (length s) + 2 <= q - 2320 -> 1 <= p ->
  (forall i w, nth_error slots i = Some w -> ro_cells ctasegs m (ap + 8 * Z.of_nat i) [C8 w]) ->
  q <= ap -> ap + 8 * Z.of_nat (length slots) + 16 < 2^63 ->
  ck_args m lo q slots args (pcx_covs fuel s args cin) -> pctx m ->
  rw_cells ctasegs m (q + -2216) DIR0 ->
  rw_cells ctasegs m (q + -104) (pcom_saved ra0 sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11) ->
  stk ctasegs m lo (q + -2240) -> lo <= q + -2320 -> kHighShadowEnd + 8 <= lo -> 2320 <= q -> q <= 2^47 -> q mod 16 = 0 ->
  mem_inv ctasegs m ->
  evt ctasegs (pcx_ret_post q lo ra0 gp tp sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 F fc m)
    (MS (mkR ra (Z_to_bv 64 (q + -2240)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 10) (Z_to_bv 64 p)
             (Z_to_bv 64 134456) (Z_to_bv 64 ap) s6 (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184)) (Z_to_bv 64 12297829382473034410)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 37) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1a98) fc None m (seg_rom ctasegs)).
Proof using RIP.
  induction fuel as [|fuel IH]; intros s args cin n q p ap lo slots ra0 sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11
    ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 F fc m
    WK BY PHI P1 VS QAP APH CKA PCX DIR SV ST LO LOLO QLO QHI Q16 MI; [discriminate WK|].
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO.
  pose proof WK as WK0. cbn [pcx_walk] in WK. destruct s as [|c s']; [discriminate WK|].
  pose proof (bytes_at_bound _ _ _ _ BY) as PB. rewrite length_zb8 in PB. cbn [length] in PB, PHI.
  pose proof (munch_refl [(q + -2320, q + -2240); (q + -2216, q + -2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM. pose proof BY as BY0.
  destruct (Z.eqb_spec c 0) as [->|NZ].
  { (* [comment removed for export] *)
    destruct (bytes_uncons m p 0 s' BY) as [CB0 _].
    assert (B0 : bytes_at ctasegs m p [z8]).
    { change [z8] with (zb8 [0]). eapply zb8_prefix with (l2 := s'). exact BY. }
    assert (C0 : bytes_at ctasegs m (q + -2180) [z8]) by (eapply (cells_byte _ _ _ 36%nat z8); [exact DIR | reflexivity | lia]).
    eapply evt_mono.
    { eapply (pcom_end_spec q p ra0 sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11); try reflexivity; try assumption. lia. }
    intros ms (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI').
    unfold pcx_ret_post. do 16 eexists. split; [reflexivity|]. split; [| split; [exact WM'| split; [exact MI'| split]]].
    - eapply munch_weaken; [| exact MU']. unfold sub_fp; cbn; intros; lia.
    - exact (stk_transport_disjoint ctasegs _ _ _ _ _ ST MU' WM' ltac:(cbn [disjoint_from]; exact I)).
    - apply rw_forget in DIR. cbn [cells_size csize Nat.add] in DIR. eexists.
      apply (rw_cells_agree ctasegs m m' _ _ DIR); [| exact WM']. apply (agree_of_munch _ _ _ _ MU'). intros xq Hxq. exact I. }
  destruct (Z.eqb_spec c 37) as [->|N37].
  2: { (* [comment removed for export] *)
    destruct ((0 <? c) && (c <? 256)) eqn:CR; [| discriminate WK]. apply andb_prop in CR. destruct CR as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
    assert (ECV : pcx_covs (S fuel) (c :: s') args cin = pcx_covs fuel s' args cin).
    { cbn [pcx_covs]. rewrite (proj2 (Z.eqb_neq c 0) NZ), (proj2 (Z.eqb_neq c 37) N37), (proj2 (Z.ltb_lt 0 c) C1), (proj2 (Z.ltb_lt c 256) C2). reflexivity. }
    rewrite ECV in CKA.
    destruct (zb8_split m p [c] s' BY) as [B1 BY'].
    eapply evt_cut.
    { eapply (pcom_scan_spec [c] p); [reflexivity| reflexivity| | exact B1| exact MI].
      cbn. rewrite (proj2 (Z.ltb_lt 0 c) C1), (proj2 (Z.ltb_lt c 256) C2). cbn. destruct (Z.eqb_spec c 37); [lia| reflexivity]. }
    cbv beta. intros ms' (a0' & ->). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in BY' |- *.
    eapply (IH s' args cin n q (p + 1) ap lo slots); try eassumption; try lia. }
  (* [comment removed for export] *)
  destruct (pcx_dir s') as [[[[ws pp] k] rest]|] eqn:PD; [| discriminate WK].
  destruct (pcx_step_inv fuel s' args cin ws pp k rest n PD WK0) as (astar & a & args2 & Ear & Lastar & FT & (n2 & WKR & En) & ECV).
  rewrite ECV in CKA. clear ECV WK. rewrite Ear in CKA.
  destruct (ck_args_split m lo q slots astar a args2 _ CKA) as (wstar & w & slots2 & Esl & Lwa & CA & CKA2).
  rewrite Lastar, skipn_app, repeat_length, Nat.sub_diag, skipn_all2 in CA by (rewrite repeat_length; lia). cbn [skipn app vhd_cov] in CA.
  rewrite Lastar, skipn_app, repeat_length, Nat.sub_diag, skipn_all2 in CKA2 by (rewrite repeat_length; lia). cbn [skipn app tl] in CKA2.
  destruct (pcx_dir_inv s' ws pp k rest PD) as (fs & wl & pl & ll & cv & Es & Ffs & WL & NF1 & PL & LL & PC & ND & WN & KS).
  destruct (pcx_conv_inv _ _ _ PC) as [CC KK].
  assert (CVND : ~ is_digit cv) by (unfold pcx_cconv in CC; unfold is_digit; lia).
  (* [comment removed for export] *)
  destruct (dsplit_app (fs ++ wl ++ pl ++ ll) cv rest CVND) as (da & db & Edd & Fda & Hdb & _).
  assert (Es2 : s' = da ++ (db ++ cv :: rest)).
  { rewrite Es. transitivity ((fs ++ wl ++ pl ++ ll) ++ cv :: rest); [rewrite <- !app_assoc; reflexivity|]. rewrite Edd, <- app_assoc. reflexivity. }
  assert (ALL : Forall (fun x => x = 45 \/ x = 48 \/ x = 42 \/ is_digit x \/ x = 108 \/ x = 46) (fs ++ wl ++ pl ++ ll)).
  { apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
    - eapply Forall_impl; [| exact Ffs]. cbn. intros x Hx. lia.
    - destruct WL as [[_ ->]|[[_ ->]|(_ & d & ds & -> & Dd & Dds)]]; [repeat constructor; lia| constructor|].
      constructor; [unfold is_digit in *; lia|]. eapply Forall_impl; [| exact Dds]. cbn; unfold is_digit; intros; lia.
    - destruct pp; cbn in PL; [subst pl; constructor | destruct PL as (d & ds & -> & Dd & Dds) | subst pl; repeat constructor; lia].
      constructor; [lia|]. constructor; [unfold is_digit in *; lia|]. eapply Forall_impl; [| exact Dds]. cbn; unfold is_digit; intros; lia.
    - destruct LL as [-> | ->]; repeat constructor; lia. }
  destruct (db ++ cv :: rest) as [|g more] eqn:Eg; [destruct db; discriminate Eg|].
  assert (G1 : 0 < g < 256 /\ ~ is_digit g /\ g <> 37 /\ g <> 36).
  { pose proof (Hdb g more eq_refl) as NDg.
    destruct db as [|d0 db']; cbn in Eg.
    - injection Eg as <- <-. unfold pcx_cconv in CC. unfold is_digit in *. lia.
    - injection Eg as -> Em. assert (IN : In g (fs ++ wl ++ pl ++ ll)) by (rewrite Edd; apply in_or_app; right; left; reflexivity).
      pose proof (proj1 (Forall_forall _ _) ALL g IN) as Hg. cbn in Hg. unfold is_digit in *. lia. }
  destruct G1 as (Gr & Gnd & G37 & G36).
  (* [comment removed for export] *)
  rewrite Es2 in BY.
  assert (BYp1 : bytes_at ctasegs m p (zb8 (37 :: da ++ [g]))).
  { apply (zb8_prefix m p (37 :: da ++ [g]) more). cbn [app]. rewrite <- app_assoc. cbn [app]. exact BY. }
  (* [comment removed for export] *)
  assert (MW : forall W ma mb mc, munch (ckW q) m ma -> munch W ma mb -> sub_fp W (ckW q) -> munch (ckW q) mb mc -> munch (ckW q) m mc).
  { intros W ma mb mc M1 M2 SB M3. apply (munch_trans _ m mb mc); [apply (munch_trans _ m ma mb); [exact M1| exact (munch_weaken _ _ _ _ SB M2)]| exact M3]. }
  assert (SB1 : sub_fp [(q + -2216, q + -2176)] (ckW q)) by (unfold sub_fp, ckW; cbn [outside]; intros; lia).
  assert (SB2 : sub_fp [(q + -2320, q + -2240)] (ckW q)) by (unfold sub_fp, ckW; cbn [outside]; intros; lia).
  assert (SB0 : sub_fp [] (ckW q)) by (unfold sub_fp, ckW; cbn [outside]; intros; exact I).
  assert (ZNS : Z.of_nat (nstarsx ws pp) = (if ws then 1 else 0) + match pp with PP_star => 1 | _ => 0 end) by (unfold nstarsx; destruct ws, pp; reflexivity).
  (* [comment removed for export] *)
  assert (TAIL : forall (wsz spz lmz : Z) (r : Z) (fw fp : word) (m4 : mem)
            (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ((wsz = 0 /\ ws = false) \/ (wsz = 1 /\ ws = true)) ->
    ((spz = 1 /\ pp = PP_star) \/ (spz = 0 /\ pp <> PP_star)) ->
    ((lmz = 0 /\ ll = []) \/ (lmz = 108 /\ ll = [108])) ->
    r = p + 1 + Z.of_nat (length (fs ++ wl ++ pl ++ ll)) + 1 ->
    (pp = PP_none -> fp = Z_to_bv 64 0) ->
    rw_cells ctasegs m4 (q + -2216) (DIRXP fw fp p r wsz spz lmz cv) ->
    munch (ckW q) m m4 -> wmono ctasegs m m4 -> mem_inv ctasegs m4 -> stk ctasegs m4 lo (q + -2240) ->
    evt ctasegs (pcx_ret_post q lo ra0 gp tp sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 F fc m)
      (MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' (Z_to_bv 64 q) s1' (Z_to_bv 64 cv) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 10)
               (Z_to_bv 64 r) (Z_to_bv 64 134456) (Z_to_bv 64 ap) (Z_to_bv 64 (r + -1)) (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184))
               (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) t3' t4' t5' t6')
          F (Z_to_bv 64 0x1b1c14) fc None m4 (seg_rom ctasegs))).
  { intros wsz spz lmz r fw fp m4 ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' WS SP LM Er FP0 DIR4 MU4 WM4 MI4 ST4.
    pose proof (agree_of_munch _ _ _ (fun x => outside (ckW q) x) MU4 (fun x H => H)) as AG4.
    assert (WSZ : wsz = 0 \/ wsz = 1) by (destruct WS; lia). assert (LMZ : lmz = 0 \/ lmz = 108) by (destruct LM; lia). assert (SPZ : spz = 0 \/ spz = 1) by (destruct SP; lia).
    assert (ZWS : zws wsz = 8 * wsz) by (destruct WSZ as [-> | ->]; reflexivity).
    assert (ZSP : zws spz = 8 * spz) by (destruct SPZ as [-> | ->]; reflexivity).
    assert (Lws : Z.of_nat (length wstar) = wsz + spz).
    { rewrite Lwa, Lastar, ZNS. destruct WS as [[-> ->]|[-> ->]]; destruct SP as [[-> ->]|[-> NS]]; try reflexivity; destruct pp; try reflexivity; exfalso; apply NS; reflexivity. }
    (* [comment removed for export] *)
    assert (SLOT : ro_cells ctasegs m4 (ap + zws wsz + zws spz) [C8 w]).
    { rewrite ZWS, ZSP. replace (ap + 8 * wsz + 8 * spz) with (ap + 8 * Z.of_nat (length wstar)) by lia.
      apply (ro_cells_agree ctasegs m m4 _ _ (VS (length wstar) w ltac:(rewrite Esl; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity))).
      apply (agree_sub _ _ _ _ AG4). intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold ckW. cbn [outside]. lia. }
    assert (APH1 : ap + 24 < 2^63) by (pose proof APH as X; rewrite Esl, length_app in X; cbn [length] in X; lia).
    (* [comment removed for export] *)
    assert (LM0 : ll = [] -> lmz = 0) by (intros E; destruct LM as [[A _]|[_ B]]; [exact A| rewrite E in B; discriminate B]).
    assert (LM1 : ll = [108] -> lmz = 108) by (intros E; destruct LM as [[_ B]|[A _]]; [rewrite E in B; discriminate B| exact A]).
    assert (EUr : 0 <= r) by lia.
    (* [comment removed for export] *)
    assert (RNE : exists c2 rest', rest = c2 :: rest') by (destruct rest as [|c2 rest']; [destruct fuel; cbn in WKR; discriminate WKR| eexists _, _; reflexivity]).
    destruct RNE as (c2 & rest' & Erest). subst rest.
    (* [comment removed for export] *)
    assert (BR : bytes_at ctasegs m r (zb8 (c2 :: rest'))).
    { assert (EL : (37 :: fs ++ wl ++ pl ++ ll ++ [cv]) ++ c2 :: rest' = 37 :: s') by (rewrite Es; cbn; rewrite <- !app_assoc; reflexivity).
      replace r with (p + Z.of_nat (length (37 :: fs ++ wl ++ pl ++ ll ++ [cv]))) by (rewrite Er; cbn [length]; rewrite !length_app; cbn [length]; lia).
      apply (proj2 (zb8_split m p (37 :: fs ++ wl ++ pl ++ ll ++ [cv]) (c2 :: rest') ltac:(rewrite EL; exact BY0))). }
    assert (LS : length s' = (length fs + length wl + length pl + length ll + 1 + length (c2 :: rest'))%nat) by (rewrite Es; repeat (rewrite length_app || cbn [length]); lia).
    rewrite !length_app in Er.
    (* [comment removed for export] *)
    assert (CKS : evt ctasegs (pck_post q r (ap + zws wsz + zws spz + 8) gp tp (Z_to_bv 64 q) (Z_to_bv 64 10) (Z_to_bv 64 134456) (Z_to_bv 64 (q + -2184))
                                (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) F fc lo m4)
      (MS (mkR ra' (Z_to_bv 64 (q + -2240)) gp tp t0' t1' t2' (Z_to_bv 64 q) s1' (Z_to_bv 64 cv) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 10)
               (Z_to_bv 64 r) (Z_to_bv 64 134456) (Z_to_bv 64 ap) (Z_to_bv 64 (r + -1)) (Z_to_bv 64 9) (Z_to_bv 64 (q + -2184))
               (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) t3' t4' t5' t6')
          F (Z_to_bv 64 0x1b1c14) fc None m4 (seg_rom ctasegs))).
    { destruct pp.
      - (* [comment removed for export] *)
        rewrite (FP0 eq_refl) in DIR4. destruct SP as [[_ X]|[-> _]]; [discriminate X|]. rewrite <- DIRX_P in DIR4.
        cbn [zws Z.eqb] in SLOT |- *. rewrite ?Z.add_0_r in SLOT |- *.
        destruct k.
        + (* [comment removed for export] *) destruct KK as [IC LMf]. destruct ll as [|l0 ll']; [| exfalso; cbn in LMf; discriminate LMf]. rewrite (LM0 eq_refl) in DIR4.
          eapply (pcx_ck_int_spec RIP q r ap lo fw p r wsz 0 cv); try reflexivity; try assumption; try lia.
        + (* [comment removed for export] *) destruct KK as [IC LMt]. destruct LM as [[-> E0]|[-> E1]]; [rewrite E0 in LMt; cbn in LMt; discriminate LMt|].
          eapply (pcx_ck_int_spec RIP q r ap lo fw p r wsz 108 cv); try reflexivity; try assumption; try lia.
        + (* [comment removed for export] *) destruct KK as [-> LMf]. destruct ll as [|l0 ll']; [| exfalso; cbn in LMf; discriminate LMf]. rewrite (LM0 eq_refl) in DIR4.
          eapply (pcx_ck_char_spec RIP q r ap lo fw p r wsz); try reflexivity; try assumption; try lia.
        + (* [comment removed for export] *) destruct KK as [-> LMf]. destruct ll as [|l0 ll']; [| exfalso; cbn in LMf; discriminate LMf]. rewrite (LM0 eq_refl) in DIR4.
          cbn [owncov] in CA.
          destruct a as [sv| |iv|uv|zv|dv]; try discriminate FT.
          * cbn [ck_arg] in CA. destruct CA as (str & CS & S0 & SSEP & SH & CK).
            rewrite <- (Z_to_bv_bv_unsigned w) in SLOT.
            assert (PCX4 : pctx m4) by (apply (pctx_munch _ m m4 PCX MU4 WM4); intros ?x ?Hx; unfold in_PCR in Hx; unfold ckW; cbn [outside]; lia).
            eapply (pcx_ck_str_spec RIP q r ap lo (bv_unsigned w) str fw p r wsz); try reflexivity; try assumption; try lia.
            -- apply (cstr_agree m m4 _ _ CS). apply (agree_sub _ _ _ _ AG4). intros x Hx. unfold ckW; cbn [outside]. unfold kHighShadowEnd in LOLO. lia.
            -- apply chkr_chk_ok. eapply chkr_agree; [exact CK|]. apply (agree_sub _ _ _ _ AG4). intros x Hx. unfold ckW; cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hx. lia.
          * cbn [ck_arg] in CA. rewrite <- (Z_to_bv_bv_unsigned w), CA in SLOT.
            eapply (pcx_ck_null_spec RIP q r ap lo fw p r wsz); try reflexivity; try assumption; try lia.
      - (* [comment removed for export] *)
        pose proof (KS ltac:(discriminate)) as EK. subst k. cbn in KK. destruct KK as [-> LMf].
        destruct ll as [|l0 ll']; [| exfalso; cbn in LMf; discriminate LMf]. rewrite (LM0 eq_refl) in DIR4.
        destruct SP as [[_ X]|[-> _]]; [discriminate X|]. cbn [zws Z.eqb] in SLOT |- *. rewrite ?Z.add_0_r in SLOT |- *.
        cbn [owncov] in CA.
        destruct a as [sv| |iv|uv|zv|dv]; try discriminate FT.
        + cbn [ck_arg] in CA. destruct CA as (str & CS & S0 & SSEP & SH & CK).
          rewrite <- (Z_to_bv_bv_unsigned w) in SLOT.
          assert (PCX4 : pctx m4) by (apply (pctx_munch _ m m4 PCX MU4 WM4); intros ?x ?Hx; unfold in_PCR in Hx; unfold ckW; cbn [outside]; lia).
          eapply (pcx_ck_strnum_spec RIP q r ap lo (bv_unsigned w) str fw fp p r wsz); try reflexivity; try assumption; try lia.
          * apply (cstr_agree m m4 _ _ CS). apply (agree_sub _ _ _ _ AG4). intros x Hx. unfold ckW; cbn [outside]. unfold kHighShadowEnd in LOLO. lia.
          * eapply chkr_agree; [exact CK|]. apply (agree_sub _ _ _ _ AG4). intros x Hx. unfold ckW; cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hx. lia.
        + cbn [ck_arg] in CA. rewrite <- (Z_to_bv_bv_unsigned w), CA in SLOT.
          replace (ap + zws wsz) with (ap + zws wsz + zws 0) in SLOT by (cbn; lia). replace (ap + zws wsz + 8) with (ap + zws wsz + zws 0 + 8) by (cbn; lia).
          eapply (pcx_ck_nullP_spec RIP q r ap lo fw fp p r wsz 0); try reflexivity; try assumption; try lia.
      - (* [comment removed for export] *)
        pose proof (KS ltac:(discriminate)) as EK. subst k. cbn in KK. destruct KK as [-> LMf].
        destruct ll as [|l0 ll']; [| exfalso; cbn in LMf; discriminate LMf]. rewrite (LM0 eq_refl) in DIR4.
        destruct SP as [[-> _]|[_ X]]; [| exfalso; apply X; reflexivity]. cbn [zws Z.eqb] in SLOT |- *.
        pose proof (bv_unsigned_in_range 64 w) as WR. unfold bv_modulus in WR. change (2 ^ Z.of_N 64) with 18446744073709551616 in WR.
        rewrite <- (Z_to_bv_bv_unsigned w) in SLOT.
        destruct (Z.eq_dec (bv_unsigned w) 0) as [W0|WNZ].
        + rewrite W0 in SLOT.
          eapply (pcx_ck_nullP_spec RIP q r ap lo fw fp p r wsz 1); try reflexivity; try assumption; try lia.
        + eapply (pcx_ck_strstar_spec RIP q r ap lo (bv_unsigned w) fw fp p r wsz); try reflexivity; try assumption; try lia. }
    eapply evt_cut; [exact CKS|]. cbv beta. clear CKS.
    intros ms5 (ra5 & u0 & u1 & u2 & s15 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & s65 & u3 & u4 & u5 & u6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & (junk5 & DIR5)).
    pose proof (MW _ _ _ _ MU4 MU5 SB2 (munch_refl _ m5)) as MU05. pose proof (wmono_trans ctasegs _ _ _ WM4 WM5) as WM05.
    pose proof (agree_of_munch _ _ _ (fun x => outside (ckW q) x) MU05 (fun x H => H)) as AG5.
    cbn [length] in LS.
    assert (BR5 : bytes_at ctasegs m5 r (zb8 (c2 :: rest'))) by (tr_fmt BR MU05).
    destruct (bytes_uncons m5 r c2 rest' BR5) as [CB2 BR5'].
    assert (EUr64 : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
    assert (C2R : 0 <= c2 < 256).
    { pose proof WKR as W2. destruct fuel as [|fuel']; [discriminate W2|]. cbn [pcx_walk] in W2.
      destruct (Z.eqb_spec c2 0); [lia|]. destruct (Z.eqb_spec c2 37); [lia|].
      destruct ((0 <? c2) && (c2 <? 256)) eqn:CR; [| discriminate W2]. apply andb_prop in CR. destruct CR as [CR1 CR2].
      apply Z.ltb_lt in CR1. apply Z.ltb_lt in CR2. lia. }
    pose proof (u8_lit c2 C2R) as EUc2.
    destruct (Z.eqb_spec c2 0) as [->|NZ2].
    { (* [comment removed for export] *)
      assert (SV5 : rw_cells ctasegs m5 (q + -104) (pcom_saved ra0 sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11)).
      { apply (rw_cells_agree ctasegs m m5 _ _ SV); [| exact WM05]. apply (agree_sub _ _ _ _ AG5). intros xq Hxq. cbn [cells_size csize pcom_saved Nat.add] in Hxq. unfold ckW; cbn [outside]. lia. }
      eapply evt_mono.
      { eapply (pcx_Lend_spec q r lo junk5 ra0); try reflexivity; try eassumption; try lia. change [z8] with (zb8 [0]). exact (zb8_prefix m5 r [0] rest' BR5). }
      intros ms (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & DJ6).
      unfold pcx_ret_post. do 16 eexists. split; [reflexivity|]. split; [exact (munch_trans _ _ _ _ MU05 MU6)|].
      split; [exact (wmono_trans ctasegs _ _ _ WM05 WM6)|]. split; [exact MI6|]. split; [exact ST6| exact DJ6]. }
    (* [comment removed for export] *)
    assert (EUs : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
    clear MU WM. pose proof (munch_refl [(q + -2320, q + -2240); (q + -2216, q + -2176)] m5) as MU. pose proof (wmono_refl ctasegs m5) as WM. try clear MI.
    unfold ckW in MU05. clear AG5 MU5 WM5 MU4 WM4 AG4.
    lstep. lstep. br2 K.
    call (pcom_setup_spec q junk5); [reflexivity| reflexivity| reflexivity| reflexivity| exact DIR5| exact Q16| lia| assumption|].
    lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) DIR0 |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR6 end.
    rename MU05 into MU06. rename WM05 into WM06. rename ST5 into ST6.
    pose proof (agree_of_munch _ _ _ (fun x => outside (ckW q) x) MU06 (fun x H => H)) as AG6.
    eapply evt_mono.
    { eapply (IH (c2 :: rest') args2 (tl (skipn (nstarsx ws pp) cin)) n2 q r (ap + zws wsz + zws spz + 8) lo slots2 ra0 sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11);
        try exact WKR; try exact DIR6; try exact ST6; try exact LOLO'; try lia.
      all: cbn [length] in LS |- *.
      all: try lia.
      all: try (rewrite Esl, length_app in APH; cbn [length] in APH; rewrite ?ZWS, ?ZSP; lia).
      all: try assumption.
      all: try (tr_fmt BR MU06).
      all: try (apply (ck_args_agree m _ lo q slots2 args2 _ CKA2 LO LOLO'); apply (agree_sub _ _ _ _ AG6); intros xq Hxq; unfold ckW; cbn [outside]; cbn in Hxq; lia).
      all: try (apply (pctx_munch _ m _ PCX MU06 WM06); intros xq Hxq; unfold in_PCR in Hxq; unfold ckW; cbn [outside]; lia).
      all: try (apply (rw_cells_agree ctasegs m _ _ _ SV); [| exact WM06]; apply (agree_sub _ _ _ _ AG6); intros xq Hxq; cbn [cells_size csize pcom_saved Nat.add] in Hxq; unfold ckW; cbn [outside]; lia).
      all: intros i wi Hn; replace (ap + zws wsz + zws spz + 8 + 8 * Z.of_nat i) with (ap + 8 * Z.of_nat (length wstar + 1 + i)) by (rewrite ZWS, ZSP; lia);
           apply (ro_cells_agree ctasegs m _ _ _ (VS (length wstar + 1 + i)%nat wi ltac:(rewrite Esl, nth_error_app2 by lia; replace (length wstar + 1 + i - length wstar)%nat with (S i) by lia; exact Hn)));
           apply (agree_sub _ _ _ _ AG6); intros xq Hxq; cbn [cells_size csize Nat.add] in Hxq; unfold ckW; cbn [outside]; rewrite ?ZWS, ?ZSP in Hxq; rewrite ?ZWS, ?ZSP; lia. }
    intros ms (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & DJ7).
    unfold pcx_ret_post. do 16 eexists. split; [reflexivity|]. split; [exact (munch_trans _ _ _ _ MU06 MU7)|].
    split; [exact (wmono_trans ctasegs _ _ _ WM06 WM7)|]. split; [exact MI7|]. split; [exact ST7| exact DJ7]. }
  (* [comment removed for export] *)
  assert (LS0 : length s' = (length da + S (length more))%nat) by (rewrite Es2, length_app; reflexivity).
  pose proof BY0 as BYs. rewrite Es in BYs.
  (* [comment removed for export] *)
  assert (Eg1 : exists g1 more1, wl ++ pl ++ ll ++ cv :: rest = g1 :: more1)
    by (destruct (wl ++ pl ++ ll ++ cv :: rest) as [|g1' more1'] eqn:E; [destruct wl; [destruct pl; [destruct ll|]|]; discriminate E| exists g1', more1'; reflexivity]).
  destruct Eg1 as (g1 & more1 & Eg1).
  assert (Hg1 : hd 0 (wl ++ pl ++ ll ++ [cv]) = g1).
  { rewrite <- (hd_app3_ne wl pl ll cv rest 0), Eg1. reflexivity. }
  rewrite Hg1 in NF1.
  assert (Bfs : bytes_at ctasegs m (p + 1) (zb8 (fs ++ [g1]))).
  { apply (zb8_window_hd m p [37] fs g1 more1). cbn [app]. rewrite <- Eg1. exact BYs. }
  assert (Eh0 : exists h0 more2, pl ++ ll ++ cv :: rest = h0 :: more2)
    by (destruct (pl ++ ll ++ cv :: rest) as [|h0' more2'] eqn:E; [destruct pl; [destruct ll|]; discriminate E| exists h0', more2'; reflexivity]).
  destruct Eh0 as (h0 & more2 & Eh0).
  assert (Hh0 : hd 0 (pl ++ ll ++ [cv]) = h0) by (rewrite <- (hd_app2_ne pl ll cv rest 0), Eh0; reflexivity).
  assert (Eh1 : exists h1 more3, ll ++ cv :: rest = h1 :: more3)
    by (destruct (ll ++ cv :: rest) as [|h1' more3'] eqn:E; [destruct ll; discriminate E| exists h1', more3'; reflexivity]).
  destruct Eh1 as (h1 & more3 & Eh1).
  assert (Hh1v : h1 = match ll with [] => cv | _ => 108 end) by (destruct LL as [-> | ->]; cbn in Eh1; congruence).
  assert (Bw : bytes_at ctasegs m (p + 1 + Z.of_nat (length fs)) (zb8 (wl ++ [h0]))).
  { replace (p + 1 + Z.of_nat (length fs)) with (p + Z.of_nat (length (37 :: fs))) by (cbn [length]; lia).
    apply (zb8_window_hd m p (37 :: fs) wl h0 more2). cbn [app]. rewrite <- Eh0. exact BYs. }
  assert (Bpl : bytes_at ctasegs m (p + 1 + Z.of_nat (length fs) + Z.of_nat (length wl)) (zb8 (pl ++ ll ++ [cv]))).
  { replace (p + 1 + Z.of_nat (length fs) + Z.of_nat (length wl)) with (p + Z.of_nat (length (37 :: fs ++ wl))) by (cbn [length]; rewrite length_app; lia).
    pose proof (zb8_split m p (37 :: fs ++ wl) (pl ++ ll ++ cv :: rest) ltac:(cbn [app]; rewrite <- app_assoc; exact BYs)) as [_ X].
    apply (zb8_prefix m _ (pl ++ ll ++ [cv]) rest). rewrite <- !app_assoc. cbn [app]. exact X. }
  assert (LSf : length s' = (length fs + length wl + length pl + length ll + 1 + length rest)%nat) by (rewrite Es; repeat (rewrite length_app || cbn [length]); lia).
  assert (G1r : 0 < g1 < 256 /\ 0 <= h0 < 256 /\ 0 <= h1 < 256).
  { assert (CVR : 0 < cv < 256) by (unfold pcx_cconv in CC; lia).
    assert (H1r : 0 < h1 < 256) by (destruct ll as [|l0 ll']; cbn in Eh1; [injection Eh1 as <- _; lia| destruct LL as [X|X]; [discriminate X| injection X as ->; injection Eh1 as <- _; lia]]).
    assert (H0r : 0 < h0 < 256).
    { destruct pp; cbn in PL; [subst pl | destruct PL as (d & ds & -> & Dd & Dds) | subst pl]; cbn [app] in Eh0.
      - rewrite Eh1 in Eh0. injection Eh0 as <- _. exact H1r.
      - injection Eh0 as <- _. lia.
      - injection Eh0 as <- _. lia. }
    split; [| lia].
    destruct WL as [[_ ->]|[[_ ->]|(_ & d & ds & -> & Dd & Dds)]]; cbn [app] in Eg1.
    - injection Eg1 as <- _. lia.
    - rewrite Eh0 in Eg1. injection Eg1 as <- _. lia.
    - injection Eg1 as <- _. unfold is_digit in Dd. lia. }
  destruct G1r as (G1r & H0r & H1r).
  assert (EUq0 : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  zidle1 BY. zidle1 BY0. zidle1 BYs. zidle1 BYp1. zidle1 Bfs. zidle1 Bw. zidle1 Bpl.
  (* [comment removed for export] *)
  unfold zidle in BYp1.
  call (pcx_p1_spec q p da g (Z_to_bv 64 0) 0 0 0 0);
    [ reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | exact Fda| exact Gr | exact Gnd| exact G37| (intros _; exact G36)| exact BYp1| (apply dir0_x; exact DIR)| (cbn [length] in PHI; lia)| lia| lia| assumption| ].
  (* [comment removed for export] *)
  unfold zidle in Bfs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (BfsC : bytes_at ctasegs mm (p + 1) (zb8 (fs ++ [g1]))) by (tr_fmt Bfs MU) end.
  cbn [length] in PHI.
  call (pcx_flags_spec fs q (p + 1) g1);
    [ reflexivity| reflexivity| (f_equal; lia)| reflexivity| exact Ffs| exact G1r| exact NF1| exact BfsC| lia| lia| assumption| ].
  clear BfsC.
  (* [comment removed for export] *)
  unfold zidle in Bw, Bpl.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BwC : bytes_at ctasegs mm (p + 1 + Z.of_nat (length fs)) (zb8 (wl ++ [h0]))) by (tr_fmt Bw MU) end.
  lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIRp end.
  destruct WL as [[-> ->]|[[-> ->]|(-> & d & ds & -> & Dd & Dds)]]; cbn [app length] in BwC, Eg1, LSf |- *.
  1: call (pcx_wstar_spec q (p + 1 + Z.of_nat (length fs)) h0 (Z_to_bv 64 0) p 0 0 0 0);
       [ reflexivity| reflexivity| reflexivity| (clear - H0r; lia)| exact BwC| exact DIRp| lia| lia| lia| assumption| ].
  2: rewrite Eh0 in Eg1; injection Eg1 as Eg1a Eg1b; subst g1;
     call (pcx_wnone_spec q (p + 1 + Z.of_nat (length fs)) h0 (Z_to_bv 64 0) p 0 0 0 0);
       [ reflexivity| reflexivity| reflexivity| reflexivity| (clear - H0r; lia)
       | (rewrite <- Hh0; exact (WN eq_refl))
       | (rewrite <- Hh0; exact ND)
       | exact BwC| exact DIRp| lia| lia| lia| assumption| ].
  3: injection Eg1 as Eg1a Eg1b; subst g1;
     call (pcx_wdig_spec q (p + 1 + Z.of_nat (length fs)) d h0 ds (Z_to_bv 64 0) p 0 0 0 0);
       [ reflexivity| (f_equal; lia)| reflexivity| reflexivity| reflexivity| reflexivity| exact Dd| exact Dds| (clear - H0r; lia)
       | (rewrite <- Hh0; exact ND)| exact BwC| exact DIRp| lia| lia| lia| lia| assumption| ].
  all: try clear BwC.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (BplC : bytes_at ctasegs mm (p + 1 + Z.of_nat (length fs) + Z.of_nat (length _)) (zb8 (pl ++ ll ++ [cv]))) by (tr_fmt Bpl MU) end.
  all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIRw end.
  all: cbn [length] in BplC |- *.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?rr) _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         lazymatch type of BplC with bytes_at _ _ ?aa _ => replace aa with rr in BplC by lia end end.
  (* [comment removed for export] *)
  all: destruct LL as [-> | ->]; cbn [app] in Hh1v; subst h1.
  all: destruct pp; cbn in PL; [subst pl | destruct PL as (dp & dsp & -> & Ddp & Ddsp) | subst pl]; cbn [app] in BplC, Eh0 |- *.
  all: first [ injection Eh0 as <- _ | rewrite Eh1 in Eh0; injection Eh0 as <- _ | idtac ].
  all: cbn [length] in LSf; rewrite ?length_app in LSf; cbn [length] in LSf.
  all: lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?rr) _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    lazymatch type of BplC with
    | bytes_at _ _ _ (zb8 [_]) =>
      call (pcx_len_spec false q rr cv);
        [ reflexivity| reflexivity| reflexivity| reflexivity| exact CC| (left; reflexivity)| exact BplC| exact DIRw| lia| lia| lia| assumption| ]
    | bytes_at _ _ _ (zb8 [108; _]) =>
      call (pcx_len_spec true q rr cv);
        [ reflexivity| reflexivity| reflexivity| reflexivity| exact CC| (left; reflexivity)| exact BplC| exact DIRw| lia| lia| lia| assumption| ]
    | bytes_at _ _ _ (zb8 [46; 42; _]) =>
      call (pcx_pstar_spec false q rr cv);
        [ reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact CC| (left; reflexivity)| exact BplC| exact DIRw| lia| lia| lia| assumption| ]
    | bytes_at _ _ _ (zb8 [46; 42; 108; _]) =>
      call (pcx_pstar_spec true q rr cv);
        [ reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact CC| (left; reflexivity)| exact BplC| exact DIRw| lia| lia| lia| assumption| ]
    | bytes_at _ _ _ (zb8 (46 :: _ :: _ ++ [_])) =>
      call (pcx_pnum_spec false q rr cv dp dsp);
        [ reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact CC| (left; reflexivity)| exact Ddp| exact Ddsp| exact BplC| exact DIRw
        | (rewrite ?length_app in *; cbn [length] in *; lia)| lia| lia| lia| assumption| ]
    | _ =>
      call (pcx_pnum_spec true q rr cv dp dsp);
        [ reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact CC| (left; reflexivity)| exact Ddp| exact Ddsp| exact BplC| exact DIRw
        | (rewrite ?length_app in *; cbn [length] in *; lia)| lia| lia| lia| assumption| ]
    end end.
  all: try match goal with H : exists fp', pclp_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp' _ _ _ _ _ _ _ |- _ => destruct H as [fpj H] end.
  all: lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR4 end.
  all: cbv zeta in DIR4; cbv zeta.
  all: try rewrite DIRX_P in DIR4.
  all: lazymatch type of DIR4 with rw_cells _ ?mm _ (DIRXP _ ?fpv _ _ _ _ _ _) =>
         eapply (TAIL _ _ _ _ _ fpv mm); [ | | | | | exact DIR4| exact MU| exact WM| assumption| exact ST] end.
  all: try (left; split; reflexivity). all: try (right; split; reflexivity). all: try (right; split; [reflexivity| discriminate]).
  all: try (intros _; reflexivity). all: try (intros X; discriminate X).
  all: cbn [length app]; repeat (rewrite length_app; cbn [length app]); lia.
Qed.

(* [comment removed for export] *)
Theorem pcom_genx_spec : forall (A : Z) (body : list Z) (args : list parg) (cin : list (option Z)) (ap lo : Z) (slots : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  pcomx_ok (body ++ [0]) args = true -> Forall (fun c => 0 < c < 256) body -> (1 <= length body)%nat ->
  bytes_at ctasegs m A (zb8 (body ++ [0])) -> A + Z.of_nat (length body) + 3 <= lo -> 1 <= A ->
  (forall i w, nth_error slots i = Some w -> ro_cells ctasegs m (ap + 8 * Z.of_nat i) [C8 w]) ->
  bv_unsigned sp <= ap -> ap + 8 * Z.of_nat (length slots) + 16 < 2^63 ->
  ck_args m lo (bv_unsigned sp) slots args (pcx_covs (length (body ++ [0])) (body ++ [0]) args cin) ->
  stk ctasegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  chk_ok m A (Z.of_nat (length body) + 1) -> pctx m -> mem_inv ctasegs m ->
  evt ctasegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1958) fc None m (seg_rom ctasegs)).
Proof using RIP.
  intros until m. intros -> -> OK FB L1 BY AB A1 VS QAP APH CKA ST LO LOLO SPH S16 CHK PCX MI.
  set (q := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO.
  unfold pcomx_ok in OK. destruct (pcx_walk (length (body ++ [0])) (body ++ [0]) args) as [n|] eqn:WK; [| discriminate OK].
  assert (CS : cstr_at m A (zb8 body)).
  { split; [rewrite zb8_app in BY; exact BY|]. intros IN. unfold zb8 in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
    pose proof (proj1 (Forall_forall _ _) FB c Hc) as R. cbn beta in R. pose proof (u8_lit c ltac:(lia)) as U. rewrite E in U. change (bv_unsigned z8) with 0 in U. lia. }
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof BY as BYf. zidle1 BYf.
  call (pcom_head_spec RIP q A ap (zb8 body) lo);
    [ reflexivity | reflexivity | reflexivity | exact ST | lia | exact LOLO' | lia | exact S16
    | exact CS | rewrite length_zb8; exact L1 | rewrite length_zb8; lia | rewrite length_zb8; exact CHK | exact PCX | exact MI | ].
  destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST1, PC0 into FRh.
  call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
  lazymatch goal with H : rw_cells ctasegs ?mm (?qq + -2216) DIR0 |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into DIR1 end.
  lazymatch type of MU with munch _ m ?mm =>
    pose proof (agree_of_munch _ _ _ (fun x => x < q + -2320 \/ q <= x) MU ltac:(intros xq Hxq; cbn beta in Hxq; cbn [outside]; lia)) as AG1 end.
  unfold zidle in BYf.
  eapply evt_mono.
  { eapply (pcx_list_spec (length (body ++ [0])) (body ++ [0]) args cin n q A ap lo slots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
      try exact WK; try exact DIR1; try exact FRh; try exact LOLO'; try assumption; try lia.
    all: try (rewrite length_app; cbn [length]; lia).
    - apply (bytes_at_agree ctasegs m _ _ _ BYf). apply (agree_sub _ _ _ _ AG1). intros xq Hxq. rewrite length_zb8, length_app in Hxq. cbn [length] in Hxq. cbn. lia.
    - intros i w Hn. apply (ro_cells_agree ctasegs m _ _ _ (VS i w Hn)). apply (agree_sub _ _ _ _ AG1). intros xq Hxq. cbn [cells_size csize Nat.add] in Hxq. cbn. lia.
    - apply (ck_args_agree m _ lo q slots args _ CKA LO LOLO' AG1).
    - lazymatch goal with |- pctx ?mm => apply (pctx_munch _ m mm PCX MU); [assumption| intros xq Hxq; unfold in_PCR in Hxq; cbn [outside]; lia] end. }
  intros ms (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & ST2 & (jd2 & DIR2)).
  lazymatch type of MU with munch _ m ?m1 =>
    pose proof (agree_of_munch _ _ _ (fun x => outside (ckW q) x) MU2 (fun x H => H)) as AG2;
    assert (FRa2 : rw_cells ctasegs m' (q + -2240) [CB 24 ja]) by
      (apply (rw_cells_agree ctasegs m1 m' _ _ FRa); [| exact WM2]; apply (agree_sub _ _ _ _ AG2); intros xq Hxq; cbn [cells_size csize Nat.add] in Hxq; unfold ckW; cbn [outside]; lia);
    assert (FRb2 : rw_cells ctasegs m' (q + -2176) [CB 2072 jb]) by
      (apply (rw_cells_agree ctasegs m1 m' _ _ FRb); [| exact WM2]; apply (agree_sub _ _ _ _ AG2); intros xq Hxq; cbn [cells_size csize Nat.add] in Hxq; unfold ckW; cbn [outside]; lia);
    assert (FRh2 : rw_cells ctasegs m' (q + -104) (pcom_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by
      (apply (rw_cells_agree ctasegs m1 m' _ _ FRh); [| exact WM2]; apply (agree_sub _ _ _ _ AG2); intros xq Hxq; cbn [cells_size csize pcom_saved Nat.add] in Hxq; unfold ckW; cbn [outside]; lia)
  end.
  release_frame FRa2 ST2 (q + -2216). release_frame DIR2 ST2 (q + -2176). release_frame FRb2 ST2 (q + -104).
  unfold pcom_saved in FRh2. release_frame FRh2 ST2 q.
  unfold pcom_post. rewrite (unsigned_lit q) by lia. do 16 eexists. split; [reflexivity|].
  split; [| split; [| split; [exact MI2| exact ST2]]].
  - lazymatch type of MU with munch _ m ?m1 => apply (munch_trans _ m m1 m'); [exact MU|] end.
    eapply munch_weaken; [| exact MU2]. unfold sub_fp, ckW; cbn [outside]; intros; lia.
  - lazymatch type of WM with wmono _ m ?m1 => exact (wmono_trans ctasegs m m1 m' WM WM2) end.
Qed.
End WithRIP.
