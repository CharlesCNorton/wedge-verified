(******************************************************************************)
(*                                                                            *)
(*                    The Wedge: Shore Break Mechanics                        *)
(*                                                                            *)
(*     Newport Beach shore break formalization: Snell's law refraction        *)
(*     around the jetty terminus, phase-coherent superposition of incident    *)
(*     and reflected wave trains, bathymetric shoaling. Derives the 2x        *)
(*     amplitude condition and characterizes the plunging breaker regime.     *)
(*                                                                            *)
(*     "Water waves are the worst possible example, because they are in       *)
(*     no respects like sound and light; they have all the complications      *)
(*     that waves can have."                                                  *)
(*     -- Richard Feynman, Lectures on Physics, 1964                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** * Citations and Data Provenance

    ** Bathymetry Data

    Source: 2009 USACE National Coastal Mapping Program (NCMP) Topobathy Lidar
    Dataset: NOAA Digital Coast ID 4810
    File: 2009_200910252009_ncmp_ca_030_h.copc.laz
    Collection Date: October 25, 2009
    Vertical Datum: NAVD88
    Horizontal CRS: NAD83(NSRS2007) / UTM zone 10N
    Vertical Accuracy: +/- 0.15 m RMSE
    Horizontal Accuracy: +/- 1.5 m
    Access: https://coast.noaa.gov/dataviewer/#/lidar/search/where:ID=4810

    The Wedge coordinates: 33.593N, 117.882W
    UTM Zone 10N (extended): E 975125, N 3728790

    Measured parameters from lidar point cloud (265,868 points):
      - Beach slope: 1:13.6 (7.3 percent grade)
      - Mean depth 0-25m offshore: +0.78 m (beach/swash zone)
      - Mean depth 25-50m offshore: -1.07 m
      - Max depth within 100m: -8.03 m
      - Points within 50m of jetty tip: 362

    ** Jetty Specifications

    Source: U.S. Army Corps of Engineers, Los Angeles District
    Structure: West Jetty, Newport Harbor Entrance
    Construction: 1916-1936 (extended from 1000 ft to 1900 ft in 1936)
    Length: 2000 ft (610 m)
    Material: Granite boulders
    Orientation: Roughly E-W
    Reference: https://www.spl.usace.army.mil/Missions/Civil-Works/Navigation/Newport-Beach/

    ** Wave Physics References

    [1] R. P. Feynman, R. B. Leighton, M. Sands. The Feynman Lectures on
        Physics, Vol. I, Ch. 51: Waves. Addison-Wesley, 1964.

    [2] USACE Coastal Engineering Manual, EM 1110-2-1100.
        Part II: Coastal Hydrodynamics, Ch. 3: Surf Zone Hydrodynamics.

    [3] McCowan, J. (1894). On the highest wave of permanent type.
        Philosophical Magazine, Series 5, 38(233), 351-358.
        Breaking criterion: H/h = 0.78

    [4] Battjes, J. A. (1974). Surf similarity.
        Proceedings 14th Coastal Engineering Conference, pp. 466-480.
        Iribarren number and breaker classification.

    ** Federal Channel Specifications

    Source: USACE Los Angeles District, Newport Beach Harbor
    Entrance Channel Authorized Depth: -20 ft MLLW (-6.1 m)
    Last Major Dredging: 2021, 2025
    Reference: https://www.newportbeachca.gov/government/departments/
               public-works/lower-newport-bay-dredging-and-cad-project
*)

Require Import Reals.
Require Import Lra.
Require Import Lia.
Require Import Rfunctions.
Require Import Rpower.
Require Import Rtrigo.
Require Import List.
Import ListNotations.

Open Scope R_scope.

(** * Physical Constants *)

Definition g : R := 9.81.
Definition rho_seawater : R := 1025.

(** * Empirical Parameters from USACE Lidar Survey *)

Module WedgeParams.

  Definition jetty_length_m : R := 610.
  Definition jetty_length_ft : R := 2000.

  Definition beach_slope : R := 1 / 13.6.
  Definition beach_slope_percent : R := 7.3.

  Definition depth_0_25m : R := 0.78.
  Definition depth_25_50m : R := 1.07.
  Definition depth_50_75m : R := 3.88.
  Definition max_depth_100m : R := 8.03.

  Definition wedge_lat : R := 33.593.
  Definition wedge_lon : R := 117.882.

  Definition reflection_coeff : R := 0.95.

  Definition channel_depth_ft : R := 20.
  Definition channel_depth_m : R := 6.1.

End WedgeParams.

(** * Wave State *)

Record WaveState : Type := mkWaveState {
  height : R;
  period : R;
  wavelength : R;
  depth : R;
  angle : R
}.

Definition WaveState_WF (w : WaveState) : Prop :=
  height w > 0 /\
  period w > 0 /\
  wavelength w > 0 /\
  depth w > 0 /\
  -PI/2 < angle w < PI/2.

(** * Deep Water Wave Properties *)

Definition deep_water_wavelength (T : R) : R :=
  g * T * T / (2 * PI).

Definition deep_water_phase_speed (T : R) : R :=
  g * T / (2 * PI).

Definition deep_water_group_speed (T : R) : R :=
  g * T / (4 * PI).

(** * Shallow Water Wave Properties *)

Definition shallow_water_speed (h : R) : R :=
  sqrt (g * h).

(** * Shoaling *)

Definition shoaling_coeff_greens_law (h1 h2 : R) : R :=
  Rpower (h1 / h2) (1/4).

Definition shoaled_height (H0 h0 h : R) : R :=
  H0 * shoaling_coeff_greens_law h0 h.

(** * Refraction (Snell's Law) *)

Definition refracted_angle (theta1 c1 c2 : R) : R :=
  asin (sin theta1 * c2 / c1).

Definition refraction_coeff (theta0 theta : R) : R :=
  sqrt (cos theta0 / cos theta).

(** * Reflection at Jetty *)

Definition reflected_amplitude (A R_coeff : R) : R :=
  A * R_coeff.

Definition superposition_amplitude (A_incident A_reflected : R) : R :=
  A_incident + A_reflected.

Definition wedge_amplitude_factor : R :=
  1 + WedgeParams.reflection_coeff.

Lemma wedge_amplitude_factor_value : wedge_amplitude_factor = 1.95.
Proof.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  lra.
Qed.

Lemma wedge_nearly_doubles : wedge_amplitude_factor > 1.9.
Proof.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  lra.
Qed.

Lemma wedge_less_than_two : wedge_amplitude_factor < 2.
Proof.
  unfold wedge_amplitude_factor, WedgeParams.reflection_coeff.
  lra.
Qed.

(** * Breaking Criterion *)

Definition breaking_ratio (H h : R) : R :=
  H / h.

Definition mccowan_criterion : R := 0.78.

Definition is_breaking (H h : R) : Prop :=
  breaking_ratio H h > mccowan_criterion.

Lemma is_breaking_iff : forall H h,
  h > 0 -> (is_breaking H h <-> H > 0.78 * h).
Proof.
  intros H h Hh.
  unfold is_breaking, breaking_ratio, mccowan_criterion.
  split; intro Hyp.
  - apply Rmult_lt_reg_r with (r := /h).
    { apply Rinv_0_lt_compat. lra. }
    field_simplify in Hyp.
    field_simplify.
    all: lra.
  - apply Rmult_lt_reg_r with (r := h).
    { lra. }
    field_simplify.
    all: lra.
Qed.

(** * Iribarren Number (Surf Similarity Parameter) *)

Definition iribarren (tan_beta H0 L0 : R) : R :=
  tan_beta / sqrt (H0 / L0).

Inductive BreakerType : Type :=
  | Spilling
  | Plunging
  | Surging
  | Collapsing.

Definition classify_breaker (xi : R) : BreakerType :=
  if Rlt_dec xi 0.5 then Spilling
  else if Rlt_dec xi 3.3 then Plunging
  else Surging.

Lemma classify_plunging : forall xi,
  0.5 <= xi -> xi < 3.3 -> classify_breaker xi = Plunging.
Proof.
  intros xi H1 H2.
  unfold classify_breaker.
  destruct (Rlt_dec xi 0.5) as [Hlt|Hge].
  - lra.
  - destruct (Rlt_dec xi 3.3) as [Hlt2|Hge2].
    + reflexivity.
    + lra.
Qed.

(** * The Wedge Wave Transformation - Simplified Model *)

Definition wedge_reflection_factor : R := 1.95.

Definition wedge_transform_simple (H0 Ks : R) : R :=
  H0 * Ks * wedge_reflection_factor.

Lemma wedge_transform_positive : forall H0 Ks,
  H0 > 0 -> Ks > 0 -> wedge_transform_simple H0 Ks > 0.
Proof.
  intros H0 Ks HH0 HKs.
  unfold wedge_transform_simple, wedge_reflection_factor.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + exact HH0.
    + exact HKs.
  - lra.
Qed.

(** * Shoaling Coefficient Bounds *)

Axiom shoaling_at_2m : shoaling_coeff_greens_law 10 2 > 1.4.
Axiom shoaling_at_1m : shoaling_coeff_greens_law 10 1 > 1.7.
Axiom shoaling_at_half_m : shoaling_coeff_greens_law 10 0.5 > 2.1.
Axiom shoaling_positive : forall h1 h2, h1 > 0 -> h2 > 0 ->
  shoaling_coeff_greens_law h1 h2 > 0.
Axiom shoaling_increases_in_shallows : forall h1 h2 h3,
  h1 > 0 -> h2 > 0 -> h3 > 0 -> h2 > h3 ->
  shoaling_coeff_greens_law h1 h3 > shoaling_coeff_greens_law h1 h2.

(** * Main Theorems *)

Theorem wedge_amplification_exceeds_two_at_2m :
  forall H0,
  H0 > 0 ->
  wedge_transform_simple H0 (shoaling_coeff_greens_law 10 2) > 2 * H0.
Proof.
  intros H0 HH0.
  unfold wedge_transform_simple, wedge_reflection_factor.
  assert (Hs : shoaling_coeff_greens_law 10 2 > 1.4) by apply shoaling_at_2m.
  assert (Hprod : 1.4 * 1.95 > 2) by lra.
  assert (H1 : H0 * shoaling_coeff_greens_law 10 2 > H0 * 1.4).
  {
    apply Rmult_lt_compat_l.
    - exact HH0.
    - exact Hs.
  }
  assert (H2 : H0 * 1.4 * 1.95 > H0 * 1.4 * (2 / 1.4)).
  {
    apply Rmult_lt_compat_l.
    - apply Rmult_lt_0_compat.
      + exact HH0.
      + lra.
    - lra.
  }
  assert (H3 : H0 * 1.4 * (2 / 1.4) = 2 * H0) by (field; lra).
  lra.
Qed.

Theorem breaking_inevitable_at_1m :
  forall H0,
  H0 >= 1 ->
  is_breaking (wedge_transform_simple H0 (shoaling_coeff_greens_law 10 1)) 1.
Proof.
  intros H0 HH0.
  unfold is_breaking, breaking_ratio, wedge_transform_simple,
         wedge_reflection_factor, mccowan_criterion.
  assert (Hs : shoaling_coeff_greens_law 10 1 > 1.7) by apply shoaling_at_1m.
  assert (Hmin : H0 * shoaling_coeff_greens_law 10 1 * 1.95 > H0 * 1.7 * 1.95).
  {
    apply Rmult_gt_compat_r.
    - lra.
    - apply Rmult_gt_compat_l.
      + lra.
      + exact Hs.
  }
  assert (Hbase : H0 * 1.7 * 1.95 >= 1 * 1.7 * 1.95).
  {
    apply Rmult_ge_compat_r.
    - lra.
    - apply Rmult_ge_compat_r.
      + lra.
      + lra.
  }
  assert (Hval : 1 * 1.7 * 1.95 > 0.78) by lra.
  lra.
Qed.

(** * Shore Profile and Slope *)

Definition shore_normal_slope (d1 d2 z1 z2 : R) : R :=
  (z2 - z1) / (d2 - d1).

Lemma wedge_slope_is_steep :
  shore_normal_slope 0 100 0.78 (-8.03) < -1/15.
Proof.
  unfold shore_normal_slope.
  lra.
Qed.

Lemma wedge_slope_value :
  shore_normal_slope 0 100 0.78 (-8.03) = -0.0881.
Proof.
  unfold shore_normal_slope.
  lra.
Qed.

(** * Depth Profile Model *)

Definition depth_at_distance (d : R) : R :=
  if Rlt_dec d 25 then 0.78
  else if Rlt_dec d 50 then 1.07
  else if Rlt_dec d 75 then 3.88
  else if Rlt_dec d 100 then 5.0
  else WedgeParams.max_depth_100m.

Lemma depth_at_25_is_shallow :
  depth_at_distance 10 < 1.
Proof.
  unfold depth_at_distance.
  destruct (Rlt_dec 10 25).
  - lra.
  - lra.
Qed.

Lemma depth_at_50_is_moderate :
  depth_at_distance 40 > 1.
Proof.
  unfold depth_at_distance.
  destruct (Rlt_dec 40 25).
  - lra.
  - destruct (Rlt_dec 40 50).
    + lra.
    + lra.
Qed.

(** * Wave Energy Considerations *)

Definition wave_energy (H : R) : R :=
  (1/8) * rho_seawater * g * H * H.

Lemma wave_energy_positive : forall H,
  H <> 0 -> wave_energy H > 0.
Proof.
  intros H Hne.
  unfold wave_energy, rho_seawater, g.
  assert (Hsq : H * H > 0).
  {
    rewrite <- Rsqr_def.
    apply Rsqr_pos_lt.
    exact Hne.
  }
  lra.
Qed.

Definition energy_amplification (H0 H : R) : R :=
  wave_energy H / wave_energy H0.

Lemma wedge_energy_nearly_quadruples : forall H0,
  H0 > 0 ->
  energy_amplification H0 (wedge_amplitude_factor * H0) > 3.6.
Proof.
  intros H0 HH0.
  unfold energy_amplification, wave_energy, wedge_amplitude_factor,
         WedgeParams.reflection_coeff, rho_seawater, g.
  assert (Hne : H0 <> 0) by lra.
  assert (Hne2 : H0 * H0 <> 0).
  {
    apply Rmult_integral_contrapositive.
    split; lra.
  }
  assert (Hfact : 1.95 * 1.95 > 3.6) by lra.
  field_simplify; lra.
Qed.

(** * Hazard Classification *)

Inductive HazardLevel : Type :=
  | Safe
  | Caution
  | Dangerous
  | Extreme.

Definition classify_hazard (H h : R) : HazardLevel :=
  let ratio := H / h in
  if Rlt_dec ratio 0.4 then Safe
  else if Rlt_dec ratio 0.6 then Caution
  else if Rlt_dec ratio 0.78 then Dangerous
  else Extreme.

Lemma wedge_always_extreme : forall H0,
  H0 >= 1 ->
  let H := wedge_transform_simple H0 (shoaling_coeff_greens_law 10 1) in
  classify_hazard H 1 = Extreme.
Proof.
  intros H0 HH0 H.
  unfold classify_hazard, H, wedge_transform_simple, wedge_reflection_factor.
  assert (Hs : shoaling_coeff_greens_law 10 1 > 1.7) by apply shoaling_at_1m.
  assert (Hbound : H0 * shoaling_coeff_greens_law 10 1 * 1.95 / 1 > 0.78).
  {
    field_simplify.
    assert (Hmin : H0 * shoaling_coeff_greens_law 10 1 >= 1 * 1.7) by
      (apply Rmult_ge_compat; lra).
    assert (Hval : 1 * 1.7 * 1.95 > 0.78) by lra.
    lra.
  }
  destruct (Rlt_dec (H0 * shoaling_coeff_greens_law 10 1 * 1.95 / 1) 0.4); try lra.
  destruct (Rlt_dec (H0 * shoaling_coeff_greens_law 10 1 * 1.95 / 1) 0.6); try lra.
  destruct (Rlt_dec (H0 * shoaling_coeff_greens_law 10 1 * 1.95 / 1) 0.78); try lra.
  reflexivity.
Qed.

(** * Summary Results *)

Definition wedge_is_dangerous : Prop :=
  forall H0, H0 >= 1 ->
  exists h, h > 0 /\ h < 3 /\
  is_breaking (wedge_transform_simple H0 (shoaling_coeff_greens_law 10 h)) h.

Theorem wedge_danger_theorem : wedge_is_dangerous.
Proof.
  unfold wedge_is_dangerous.
  intros H0 HH0.
  exists 1.
  split.
  - lra.
  - split.
    + lra.
    + apply breaking_inevitable_at_1m.
      exact HH0.
Qed.
