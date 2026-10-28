(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS ITree Nodes. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface FX_lib F_pop_arg F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive pcx_kind : Type := PK_int | PK_long | PK_char | PK_str.
Inductive pcx_prec : Type := PP_none | PP_num | PP_star.

Definition pcx_isdigit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition pcx_isflag (c : Z) : bool := (c =? 45) || (c =? 48).

Fixpoint pcx_flags (s : list Z) : list Z :=
  match s with c :: s' => if pcx_isflag c then pcx_flags s' else s | [] => [] end.
Fixpoint pcx_digits (s : list Z) : list Z :=
  match s with c :: s' => if pcx_isdigit c then pcx_digits s' else s | [] => [] end.

Definition pcx_conv (lm : bool) (c : Z) : option pcx_kind :=
  if (c =? 100) || (c =? 105) || (c =? 117) || (c =? 120) || (c =? 88) then Some (if lm then PK_long else PK_int)
  else if lm then None
  else if c =? 99 then Some PK_char
  else if c =? 115 then Some PK_str
  else None.

(* [comment removed for export] *)
Definition pcx_precp (s : list Z) : option (pcx_prec * list Z) :=
  match s with
  | 46 :: 42 :: s' => match s' with c :: _ => if pcx_isdigit c then None else Some (PP_star, s') | [] => None end
  | 46 :: s' => match s' with c :: _ => if pcx_isdigit c then Some (PP_num, pcx_digits s') else None | [] => None end
  | _ => Some (PP_none, s)
  end.

(* [comment removed for export] *)
Definition pcx_dir (s : list Z) : option (bool * pcx_prec * pcx_kind * list Z) :=
  let s1 := pcx_flags s in
  let '(ws, s2) := match s1 with 42 :: s' => (true, s') | _ => (false, pcx_digits s1) end in
  match pcx_precp s2 with
  | None => None
  | Some (pp, s3) =>
      let '(lm, s4) := match s3 with 108 :: s' => (true, s') | _ => (false, s3) end in
      match s4 with
      | c :: s5 => match pcx_conv lm c with
                   | Some k => match pp, k with PP_none, _ => Some (ws, pp, k, s5) | _, PK_str => Some (ws, pp, k, s5) | _, _ => None end
                   | None => None
                   end
      | [] => None
      end
  end.

(* [comment removed for export] *)
Definition pcx_fits (k : pcx_kind) (a : parg) : bool :=
  match k, a with
  | PK_str, PA_s _ => true | PK_str, PA_sn => true | PK_str, _ => false
  | _, PA_s _ => false | _, PA_sn => false | _, _ => true
  end.

(* [comment removed for export] *)
Fixpoint pcx_walk (fuel : nat) (s : list Z) (args : list parg) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      match s with
      | [] => None
      | c :: s' =>
          if c =? 0 then Some 0%nat
          else if c =? 37 then
            match pcx_dir s' with
            | None => None
            | Some (ws, pp, k, rest) =>
                match (if ws then match args with _ :: t => Some t | [] => None end else Some args) with
                | None => None
                | Some args1 =>
                    match (match pp with PP_star => match args1 with _ :: t => Some t | [] => None end | _ => Some args1 end) with
                    | None => None
                    | Some args2 =>
                        match args2 with
                        | a :: args3 =>
                            if pcx_fits k a then
                              match pcx_walk fuel' rest args3 with
                              | Some n => Some ((if ws then 1 else 0) + (match pp with PP_star => 1 | _ => 0 end) + 1 + n)%nat
                              | None => None
                              end
                            else None
                        | [] => None
                        end
                    end
                end
            end
          else if (0 <? c) && (c <? 256) then pcx_walk fuel' s' args
          else None
      end
  end.

Definition pcomx_ok (fmt : list Z) (args : list parg) : bool :=
  match pcx_walk (length fmt) fmt args with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition vhd_cov (covs : list (option Z)) : option Z := match covs with [] => None | c :: _ => c end.
Fixpoint pcx_covs (fuel : nat) (s : list Z) (args : list parg) (covs : list (option Z)) : list (option Z) :=
  match fuel with
  | O => []
  | S fuel' =>
      match s with
      | [] => []
      | c :: s' =>
          if c =? 0 then []
          else if c =? 37 then
            match pcx_dir s' with
            | None => []
            | Some (ws, pp, k, rest) =>
                match (if ws then match args with _ :: t => Some (t, tl covs) | [] => None end else Some (args, covs)) with
                | None => []
                | Some (args1, covs1) =>
                    match (match pp with PP_star => match args1 with _ :: t => Some (t, tl covs1) | [] => None end | _ => Some (args1, covs1) end) with
                    | None => []
                    | Some (args2, covs2) =>
                        match args2 with
                        | a :: args3 =>
                            (if ws then [None] else []) ++ (match pp with PP_star => [None] | _ => [] end)
                            ++ (match pp, k with PP_star, PK_str => vhd_cov covs2 | _, _ => None end)
                            :: pcx_covs fuel' rest args3 (tl covs2)
                        | [] => []
                        end
                    end
                end
            end
          else if (0 <? c) && (c <? 256) then pcx_covs fuel' s' args covs
          else []
      end
  end.

(* [comment removed for export] *)
Definition vcovs (fmt : list Z) (args : list parg) : list (option Z) :=
  pcx_covs (length fmt) fmt args (arg_covs (length fmt) fmt args).

(* [comment removed for export] *)
Definition fmtz_ok (fmt : list Z) : bool :=
  (2 <=? length fmt)%nat && forallb (fun c => (0 <? c) && (c <? 256)) (removelast fmt) && (last fmt 1 =? 0).

Lemma fmtz_ok_body : forall fmt, fmtz_ok fmt = true ->
  exists body, fmt = body ++ [0] /\ Forall (fun c => 0 < c < 256) body /\ (1 <= length body)%nat.
Proof.
  intros fmt H. unfold fmtz_ok in H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  destruct fmt as [|c0 fmt0]; [cbn in H1; discriminate|].
  pose proof (app_removelast_last 1 (ltac:(discriminate) : c0 :: fmt0 <> [])) as E.
  exists (removelast (c0 :: fmt0)). split; [| split].
  - rewrite E at 1. f_equal. f_equal. apply Z.eqb_eq in H3. exact H3.
  - apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) H2 c Hc) as R. cbn beta in R.
    apply andb_prop in R. destruct R as [R1 R2]. apply Z.ltb_lt in R1. apply Z.ltb_lt in R2. lia.
  - apply Nat.leb_le in H1. rewrite E, length_app in H1. cbn [length] in H1. lia.
Qed.

Local Open Scope string_scope. Local Open Scope list_scope. Local Open Scope Z_scope.
(* [comment removed for export] *)
Example pcomx_ok_C16 : forall mon mday hour min sec f year,      (* [comment removed for export] *)
  pcomx_ok (str "%s %2d %02d:%02d:%02d.%.*s %d GMT" ++ [0]) [PA_s mon; PA_i mday; PA_i hour; PA_i min; PA_i sec; PA_i 3; PA_s f; PA_i year] = true.
Proof. intros. reflexivity. Qed.
Example vcovs_C16 : forall mon mday hour min sec f year,        (* [comment removed for export] *)
  vcovs (str "%s %2d %02d:%02d:%02d.%.*s %d GMT" ++ [0]) [PA_s mon; PA_i mday; PA_i hour; PA_i min; PA_i sec; PA_i 3; PA_s f; PA_i year]
  = [None; None; None; None; None; None; Some 3; None].
Proof. intros. reflexivity. Qed.
Example pcomx_ok_C18 : forall g ms, pcomx_ok (str "%.14s.%03dZ" ++ [0]) [PA_s g; PA_i ms] = true.   (* [comment removed for export] *)
Proof. intros. reflexivity. Qed.
Example vcovs_C18 : forall g ms, vcovs (str "%.14s.%03dZ" ++ [0]) [PA_s g; PA_i ms] = [None; None].   (* [comment removed for export] *)
Proof. intros. reflexivity. Qed.
Example pcomx_ok_C18_null : forall ms, pcomx_ok (str "%.14s.%03dZ" ++ [0]) [PA_sn; PA_i ms] = true.
Proof. intros. reflexivity. Qed.
Example pcomx_ok_C17 : forall y mo d h mi s,                     (* [comment removed for export] *)
  pcomx_ok (str "%04d%02d%02d%02d%02d%02dZ" ++ [0]) [PA_i y; PA_i mo; PA_i d; PA_i h; PA_i mi; PA_i s] = true.
Proof. intros. reflexivity. Qed.
Example pcomx_ok_C1 : pcomx_ok (str "%*sSigned Certificate Timestamp:" ++ [0]) [PA_i 4; PA_s []] = true.
Proof. reflexivity. Qed.
Example vcovs_C1 : vcovs (str "%*sSigned Certificate Timestamp:" ++ [0]) [PA_i 4; PA_s []] = [None; None].
Proof. reflexivity. Qed.
Example pcomx_ok_C13 : forall b, pcomx_ok (str "%02X:" ++ [0]) [PA_u b] = true.
Proof. intros. reflexivity. Qed.
Example pcomx_ok_F1 : forall a b c d s,
  pcomx_ok [37;53;108;100;58;100;61;37;45;50;100;32;104;108;61;37;108;100;32;108;61;37;52;108;100;32;37;115;0]
           [PA_z a; PA_i b; PA_z c; PA_z d; PA_s s] = true.
Proof. intros. reflexivity. Qed.
Example pcomx_ok_F15 : forall i s u, pcomx_ok [37;42;115;37;48;52;120;32;45;32;0] [PA_i i; PA_s s; PA_u u] = true.
Proof. intros. reflexivity. Qed.
(* [comment removed for export] *)
Example pcomx_rej_pd : forall i, pcomx_ok (str "%.3d" ++ [0]) [PA_i i] = false.
Proof. intros. reflexivity. Qed.
Example pcomx_rej_pdot : forall s, pcomx_ok (str "%.s" ++ [0]) [PA_s s] = false.
Proof. intros. reflexivity. Qed.
Example fmtz_ok_C18 : fmtz_ok (str "%.14s.%03dZ" ++ [0]) = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_vsnprintf : Z := 0x1ad66c.     (* [comment removed for export] *)
Definition e_snprintf : Z := 0x1ad674.      (* [comment removed for export] *)

Section PrintfContracts.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition varg_ok (Σ : rts RT) (m : mem) (sp : word) (lo D n : Z) (slot : word) (a : parg) : Prop :=
  match a with
  | PA_s s => exists slack : list byte,
      bytes_at ctasegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
      /\ Forall (fun c => 0 < c < 256) s /\ zlength s + 1 <= 2^40     (* [comment removed for export] *)
      /\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
      /\ 0 < bv_unsigned slot /\ bv_unsigned slot + zlength s + 1 + zlength slack <= USTACK_TOP - 16
      /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned slot)
      /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= D \/ D + n <= bv_unsigned slot)
      /\ acc ctasegs m (bv_unsigned slot) (zlength s + 1)
      /\ rng_class RT Σ (bv_unsigned slot) (zlength s + 1)
  | PA_sn => bv_unsigned slot = 0
  | PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
  | PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
  | PA_z u => bv_unsigned slot = u
  | PA_g _ => False
  end.

Fixpoint vargs_ok (Σ : rts RT) (m : mem) (sp : word) (lo D n : Z) (slots : list word) (args : list parg) : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => False
                  | w :: slots' => varg_ok Σ m sp lo D n w a /\ vargs_ok Σ m sp lo D n slots' args'
                  end
  end.

(* [comment removed for export] *)
Definition varg_okx (Σ : rts RT) (m : mem) (sp : word) (lo D n : Z) (slot : word) (a : parg) (cov : option Z) : Prop :=
  match a with
  | PA_s s =>
      varg_ok Σ m sp lo D n slot a
      \/ (exists p, cov = Some p /\ 0 < p <= zlength s
             /\ bytes_at ctasegs m (bv_unsigned slot) (zb s)
             /\ Forall (fun c => 0 < c < 256) s /\ zlength s + 1 <= 2^40
             /\ 0 < bv_unsigned slot /\ bv_unsigned slot + zlength s <= USTACK_TOP - 16
             /\ (bv_unsigned slot + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned slot)
             /\ (bv_unsigned slot + zlength s <= D \/ D + n <= bv_unsigned slot)
             /\ acc ctasegs m (bv_unsigned slot) p /\ rng_class RT Σ (bv_unsigned slot) p)
  | _ => varg_ok Σ m sp lo D n slot a
  end.

Fixpoint vargs_okx (Σ : rts RT) (m : mem) (sp : word) (lo D n : Z) (slots : list word) (args : list parg)
                   (covs : list (option Z)) : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => False
                  | w :: slots' => varg_okx Σ m sp lo D n w a (vhd_cov covs) /\ vargs_okx Σ m sp lo D n slots' args' (tl covs)
                  end
  end.

Lemma varg_ok_okx : forall Σ m sp lo D n w a cov, varg_ok Σ m sp lo D n w a -> varg_okx Σ m sp lo D n w a cov.
Proof. intros Σ m sp lo D n w a cov H. destruct a; cbn [varg_okx]; try exact H. left. exact H. Qed.

Lemma vargs_ok_okx : forall Σ m sp lo D n slots args covs,
  vargs_ok Σ m sp lo D n slots args -> vargs_okx Σ m sp lo D n slots args covs.
Proof.
  intros Σ m sp lo D n slots args. revert slots. induction args as [|a args IH]; intros slots covs H; [destruct slots; exact I|].
  cbn [vargs_ok vargs_okx] in *. destruct slots as [|w slots']; [exact H|]. destruct H as [H1 H2].
  split; [apply varg_ok_okx; exact H1 | apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Definition vfmt_ok (m : mem) (A : Z) (fmt : list Z) (args : list parg) (o : list Z) : Prop :=
  bytes_at ctasegs m A (zb fmt) /\ Forall (fun c => 0 <= c < 256) fmt
  /\ 0x10000 <= A /\ A + zlength fmt <= STATIC_SPLIT
  /\ acc ctasegs m A (zlength fmt)
  /\ pass1x_ok fmt = true
  /\ printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (zlength o, o))
  /\ fp_callsx (length fmt) fmt args = []
  /\ pcomx_ok fmt args = true
  /\ fmtz_ok fmt = true.

(* [comment removed for export] *)
Definition vsn_post (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (D : Z) (o : list Z) (lo : Z) (m : mem) : config -> Prop :=
  ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (zlength o)) m' ms
                    /\ rt_after RT Σ (bv_unsigned sp) lo m m'
                    /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) D (zlength o + 1) m m'
                    /\ bytes_at ctasegs m' D (zb o ++ [Z_to_bv 8 0])).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vsnprintf_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (D n A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (o : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
  vfmt_ok m A fmt args o ->
  (* [comment removed for export] *)
  va_area m VA slots -> bv_unsigned sp <= VA -> VA + 8 * zlength slots <= USTACK_TOP - 16 ->
  (D + n <= VA \/ VA + 8 * zlength slots <= D) ->
  vargs_okx Σ m sp lo D n slots args (vcovs fmt args) ->
  (* [comment removed for export] *)
  1 <= n -> n < 2^31 -> zlength o <= n - 1 -> 0 < D -> D + n <= USTACK_TOP - 16 -> (D + n <= 0x10000 \/ SEGTOP_A <= D) ->
  checked_dst RT Σ m sp D n ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_vsnprintf m)))
    (vsn_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 D o lo m).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition snprintf_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (D n A : Z) (fmt : list Z) (stk : list word) (args : list parg) (o : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
  vfmt_ok m A fmt args o ->
  va_area m (bv_unsigned sp) stk -> bv_unsigned sp + 8 * zlength stk <= USTACK_TOP - 16 ->
  (stk = [] \/ D + n <= bv_unsigned sp \/ bv_unsigned sp + 8 * zlength stk <= D) ->
  vargs_okx Σ m sp lo D n ([a3; a4; a5; a6; a7] ++ stk) args (vcovs fmt args) ->
  1 <= n -> n < 2^31 -> zlength o <= n - 1 -> 0 < D -> D + n <= USTACK_TOP - 16 -> (D + n <= 0x10000 \/ SEGTOP_A <= D) ->
  checked_dst RT Σ m sp D n ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_snprintf m)))
    (vsn_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 D o lo m).

End PrintfContracts.

(* [comment removed for export] *)
Record printf_contracts (RT : rt_sig) : Prop := mkPFC {
  rc_vsnprintf : vsnprintf_icontract RT;
  rc_snprintf : snprintf_icontract RT
}.
